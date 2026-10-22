package io.joern.c2cpg.passes

import io.joern.c2cpg.C2Cpg
import io.joern.c2cpg.Config
import io.joern.c2cpg.astcreation.AstCreator
import io.joern.c2cpg.parser.CdtParser
import io.joern.c2cpg.parser.CdtParser.HeaderFileParserLanguage
import io.joern.c2cpg.parser.FileDefaults
import io.joern.c2cpg.parser.HeaderFileFinder
import io.joern.c2cpg.parser.JSONCompilationDatabaseParser
import io.joern.c2cpg.parser.JSONCompilationDatabaseParser.CompilationDatabase
import io.joern.x2cpg.SourceFiles
import io.joern.x2cpg.utils.{Report, TimeUtils}
import io.shiftleft.codepropertygraph.generated.Cpg
import io.shiftleft.codepropertygraph.generated.nodes.{NewCall, NewTypeDecl}
import io.shiftleft.passes.ForkJoinParallelCpgPassWithAccumulator
import org.apache.commons.lang3.StringUtils
import org.eclipse.cdt.core.dom.ast.gnu.cpp.GPPLanguage
import org.eclipse.cdt.core.model.ILanguage
import org.slf4j.{Logger, LoggerFactory}

import java.nio.file.{Path, Paths}
import scala.collection.immutable.ListMap
import scala.collection.mutable

object AstCreationPass {

  /** Where a struct, union or class is defined: the file CDT read the definition from, the offset of its specifier
    * there, the specifier's offset in the macro expansion it starts in (-1 if it starts in the file itself), and the
    * name the specifier gives the type as CDT reads it (empty if anonymous). It is the same in every translation unit
    * that sees the definition.
    */
  final case class DeclarationPlace(file: String, offset: Int, offsetInMacroExpansion: Int, name: String)

  /** The TYPE_DECL made for the definition at a [[DeclarationPlace]], whether the file it was made from was parsed as
    * C++ (a header may be parsed both as C and as C++), and whether it was made by the parse of the file that holds the
    * definition. c2cpg also lowers the declarations of an `extern "C"` block that come from a header the block
    * includes, so a C++ file's parse can make another TYPE_DECL for a header's struct.
    */
  final case class PlacedTypeDecl(typeDecl: NewTypeDecl, isCpp: Boolean, fromOwnFile: Boolean)

  /** A field access whose field CDT resolved: the access, the place of the definition of the field's struct, union or
    * class, the field's name, the line of the field's declarator, and whether the access's file was parsed as C++.
    */
  final case class ResolvedFieldAccess(
    access: NewCall,
    place: DeclarationPlace,
    member: String,
    memberLine: Option[Int],
    isCpp: Boolean
  )

  // LinkedHash* collections: ForkJoinParallelCpgPassWithAccumulator merges accumulators in
  // part (i.e. sorted file) order, so insertion order — and thus iteration order — is
  // deterministic across runs. mergeWith must stay associative for this to hold.
  case class Accumulator(
    usedTypes: mutable.LinkedHashSet[String] = mutable.LinkedHashSet.empty,
    methodDeclarations: mutable.LinkedHashMap[String, FunctionDeclNodePass.MethodInfo] = mutable.LinkedHashMap.empty,
    methodDefinitions: mutable.LinkedHashSet[String] = mutable.LinkedHashSet.empty,
    headerIncludes: mutable.LinkedHashMap[String, HeaderFileParserLanguage] = mutable.LinkedHashMap.empty,
    typeDecls: mutable.LinkedHashMap[DeclarationPlace, mutable.ArrayBuffer[PlacedTypeDecl]] =
      mutable.LinkedHashMap.empty,
    fieldAccesses: mutable.ArrayBuffer[ResolvedFieldAccess] = mutable.ArrayBuffer.empty
  ) {
    def registerType(typeName: String): Unit = usedTypes.add(typeName)

    def registerTypeDecl(place: DeclarationPlace, typeDecl: PlacedTypeDecl): Unit =
      typeDecls.getOrElseUpdate(place, mutable.ArrayBuffer.empty).addOne(typeDecl)

    def registerFieldAccess(access: ResolvedFieldAccess): Unit = fieldAccesses.addOne(access)

    def registerMethodDeclaration(fullName: String, methodInfo: FunctionDeclNodePass.MethodInfo): Unit = {
      methodDeclarations.getOrElseUpdate(fullName, methodInfo)
    }

    def registerMethodDefinition(fullName: String): Unit = methodDefinitions.add(fullName)

    /** Updates the parser language information for a header file.
      *
      * This method tracks which language parser (C, C++, or both) should be used for each header file based on where
      * the header is included from. The logic follows:
      *   - If first time seen: Use C parser for headers included from C files, C++ parser for others
      *   - If previously seen in C files only: Keep C parser or upgrade to both parsers if included from C++
      *   - If previously seen in C++ files only: Keep C++ parser or upgrade to both parsers if included from C
      *   - If already seen in both C and C++ files: Keep using both parsers
      *
      * @param foundPath
      *   The full path to the header file being processed
      * @param language
      *   The language to parse it with
      */
    def updateHeaderFileParserLanguage(foundPath: String, language: HeaderFileParserLanguage): Unit = {
      headerIncludes.updateWith(foundPath) {
        case None                           => Some(language)
        case Some(prev) if prev != language => Some(HeaderFileParserLanguage.Both)
        case some                           => some
      }
    }

    def mergeWith(other: Accumulator): Unit = {
      usedTypes ++= other.usedTypes
      other.methodDeclarations.foreach { case (k, v) => methodDeclarations.getOrElseUpdate(k, v) }
      methodDefinitions ++= other.methodDefinitions
      other.headerIncludes.foreach { case (path, lang) => updateHeaderFileParserLanguage(path, lang) }
      other.typeDecls.foreach { case (place, placed) =>
        typeDecls.getOrElseUpdate(place, mutable.ArrayBuffer.empty).addAll(placed)
      }
      fieldAccesses.addAll(other.fieldAccesses)
    }
  }

}

class AstCreationPass(
  cpg: Cpg,
  preprocessedFiles: List[String],
  fileExtensions: Set[String],
  config: Config,
  previousAccumulator: Option[AstCreationPass.Accumulator] = None,
  report: Report = new Report()
) extends ForkJoinParallelCpgPassWithAccumulator[(Path, ILanguage), AstCreationPass.Accumulator](cpg) {

  import AstCreationPass.Accumulator

  private val compilationDatabase: Option[CompilationDatabase] =
    config.compilationDatabaseFilename.flatMap(JSONCompilationDatabaseParser.parse)

  private val logger: Logger = LoggerFactory.getLogger(classOf[AstCreationPass])

  private val headerFileFinder: HeaderFileFinder = new HeaderFileFinder(config)
  private val cdtParser: CdtParser               = new CdtParser(config, headerFileFinder, compilationDatabase)

  private var _finalAccumulator: Accumulator = Accumulator()

  def accumulatedState(): Accumulator = _finalAccumulator

  def typesSeen(): Set[String] = _finalAccumulator.usedTypes.toSet

  // ListMap preserves the accumulator's deterministic insertion order; `toMap` would
  // re-hash into an unordered immutable.HashMap
  def unhandledMethodDeclarations(): Map[String, FunctionDeclNodePass.MethodInfo] =
    ListMap.from(_finalAccumulator.methodDeclarations.filterNot { case (k, _) =>
      _finalAccumulator.methodDefinitions.contains(k)
    })

  def headerIncludes(): Map[String, HeaderFileParserLanguage] = _finalAccumulator.headerIncludes.toMap

  def typeDeclsByPlace()
    : collection.Map[AstCreationPass.DeclarationPlace, collection.Seq[AstCreationPass.PlacedTypeDecl]] =
    _finalAccumulator.typeDecls

  def fieldAccesses(): collection.Seq[AstCreationPass.ResolvedFieldAccess] = _finalAccumulator.fieldAccesses

  override def createAccumulator(): Accumulator = Accumulator()

  override def mergeAccumulator(left: Accumulator, right: Accumulator): Unit = left.mergeWith(right)

  override def onAccumulatorComplete(builder: DiffGraphBuilder, accumulator: Accumulator): Unit = {
    previousAccumulator.foreach(accumulator.mergeWith)
    _finalAccumulator = accumulator
  }

  override def generateParts(): Array[(Path, ILanguage)] = {
    val sourceFiles = if (config.compilationDatabaseFilename.isEmpty) {
      sourceFilesFromDirectory()
    } else {
      sourceFilesFromCompilationDatabase(config.compilationDatabaseFilename.get)
    }
    sourceFiles.flatMap { file =>
      val path = Paths.get(file).toAbsolutePath
      CdtParser.languageMappingForSourceFile(path, previousAccumulator.fold(Map.empty)(_.headerIncludes.toMap), config)
    }
  }

  private def sourceFilesFromDirectory(): Array[String] = {
    val allSourceFiles = SourceFiles
      .determine(
        config.inputPath,
        fileExtensions,
        ignoredDefaultRegex = Option(C2Cpg.DefaultIgnoredFolders),
        ignoredFilesRegex = Option(config.ignoredFilesRegex),
        ignoredFilesPath = Option(config.ignoredFiles)
      )
      .toArray
    if (config.withPreprocessedFiles) {
      allSourceFiles.filter {
        case f if !FileDefaults.hasPreprocessedFileExtension(f) =>
          val fAsPreprocessedFile = s"${f.substring(0, f.lastIndexOf("."))}${FileDefaults.PreprocessedExt}"
          !preprocessedFiles.exists { sourceFile => f != sourceFile && sourceFile == fAsPreprocessedFile }
        case _ => true
      }
    } else {
      allSourceFiles
    }
  }

  private def sourceFilesFromCompilationDatabase(compilationDatabaseFile: String): Array[String] = {
    compilationDatabase match {
      case Some(db) =>
        val files         = db.commands.map(_.compiledFile()).toList
        val filteredFiles = files.filter(f => fileExtensions.exists(StringUtils.endsWithIgnoreCase(f, _)))
        SourceFiles
          .filterFiles(
            filteredFiles,
            config.inputPath,
            ignoredDefaultRegex = Option(C2Cpg.DefaultIgnoredFolders),
            ignoredFilesRegex = Option(config.ignoredFilesRegex),
            ignoredFilesPath = Option(config.ignoredFiles)
          )
          .toArray
      case None =>
        logger.warn(s"'$compilationDatabaseFile' contains no source files. CPG will be empty.")
        Array.empty
    }
  }

  private def suffixFromLanguage(relPath: String, language: ILanguage): String = {
    if (FileDefaults.hasCHeaderFileExtension(relPath) && language.isInstanceOf[GPPLanguage]) { "<cpp>" }
    else ""
  }

  override def runOnPart(
    diffGraph: DiffGraphBuilder,
    fileAndLanguage: (Path, ILanguage),
    accumulator: Accumulator
  ): Unit = {
    val (path, language)   = fileAndLanguage
    val relPath            = SourceFiles.toRelativePath(path.toString, config.inputPath)
    val (gotCpg, duration) = TimeUtils.time {
      val parseResult = cdtParser.parse(path, language, accumulator)
      parseResult match {
        case Some(translationUnit) =>
          val fileLOC = translationUnit.getRawSignature.linesIterator.size
          report.addReportInfo(relPath, fileLOC, parsed = true)
          try {
            val languageSuffix = suffixFromLanguage(relPath, language)
            val localDiff      =
              new AstCreator(relPath, accumulator, config, translationUnit, headerFileFinder, languageSuffix)(
                config.schemaValidation
              ).createAst()
            diffGraph.absorb(localDiff)
            logger.debug(s"Processed ‘$relPath’")
            true
          } catch {
            case s: StackOverflowError =>
              /**   - Eclipse CDT’s C/C++ type inference/analysis is heavily recursive. For certain real-world inputs
                *     this can create extremely deep call stacks and trigger a JVM `StackOverflowError`.
                *   - `StackOverflowError` is a `VirtualMachineError`. Without an explicit catch, failing type analysis
                *     in a single problematic file would crash the whole process.
                */
              logger.warn(s"Failed to process ‘$relPath’", s)
              false
            case other: Throwable =>
              logger.warn(s"Failed to process ‘$relPath’", other)
              false
          }
        case None =>
          false
      }
    }
    report.updateReport(relPath, gotCpg, duration)
  }

}
