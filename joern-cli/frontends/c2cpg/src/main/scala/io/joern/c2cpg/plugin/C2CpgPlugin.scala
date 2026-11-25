package io.joern.c2cpg.plugin

import io.joern.c2cpg.Config
import io.joern.x2cpg.plugin.{FrontendPlugin, FrontendPlugins}
import io.shiftleft.codepropertygraph.generated.{DiffGraphBuilder, EdgeTypes}
import io.shiftleft.codepropertygraph.generated.nodes.{AstNodeNew, NewNode, NewTag}
import org.eclipse.cdt.core.dom.ast.{IASTNode, IASTTranslationUnit}
import org.eclipse.cdt.core.parser.{FileContent, IScannerInfo}

import java.nio.file.Path

import scala.collection.mutable

/** A plug-in of c2cpg: code that a plug-in jar provides, which reads what CDT parsed and what c2cpg built from it, and
  * writes to the graph before any overlay runs.
  *
  * What every frontend's plug-ins share (name, version, settings, loading by name, failure isolation, [[onGraph]]) is
  * x2cpg's [[io.joern.x2cpg.plugin.FrontendPlugin]]; this adds the calls c2cpg makes while it builds the graph. A
  * plug-in jar goes in c2cpg's lib folder, and the plug-in runs when it is named with `--plugin <name>`, or when it is
  * passed directly in [[io.joern.c2cpg.Config.plugins]]. c2cpg calls [[configure]] once with the plug-in's settings
  * (`--plugin-arg <name>.<key>=<value>`), then [[onTranslationUnit]] once for every file it translates, and [[onGraph]]
  * once after its own passes, before any overlay. Before CDT parses a file, c2cpg also asks it for the file's defines
  * and include paths ([[scannerInfo]]), the file's text ([[fileContent]]) and the content of each include
  * ([[includeContent]]); what these return is what CDT parses. While c2cpg reads each parameter it asks for the
  * parameter's tags ([[parameterTags]]), which it writes on the parameter's node. Each graph call gets a diff graph of
  * its own; c2cpg applies it only if the call returns normally, so a failing plug-in loses its own writes and never
  * c2cpg's graph.
  *
  * What a plug-in writes is its own business. The overlays that run after c2cpg derive control flow, the call graph and
  * data flow from the AST, and assume what c2cpg guarantees: every AST node has an ORDER that is its evaluation order,
  * arguments are numbered from 1 by ARGUMENT_INDEX and are AST children too, every TYPE_FULL_NAME has a TYPE node, and
  * no edge the overlays derive (CFG, CONTAINS, EVAL_TYPE, CALL, ...) exists yet. A plug-in that adds or changes AST
  * nodes keeps these.
  *
  * c2cpg translates files in parallel, so [[onTranslationUnit]] is called from several threads at once and must not
  * share mutable state between calls. What it writes for a file is applied in file order, after c2cpg's own nodes for
  * that file, so the graph is the same from run to run when the plug-in's writes depend only on the file it is given.
  */
trait C2CpgPlugin extends FrontendPlugin {

  /** The plug-in configured with `settings`; called once per run, before any file is parsed. */
  override def configure(settings: Map[String, String]): C2CpgPlugin = this

  /** Called before CDT parses `file`, with the defines and include paths c2cpg chose for it; CDT gets what this
    * returns. Called for every parse, including c2cpg's re-parse of a statement CDT could not parse.
    */
  def scannerInfo(file: Path, info: IScannerInfo): IScannerInfo = info

  /** Called before CDT parses `file`, with its text; CDT parses what this returns. */
  def fileContent(file: Path, content: FileContent): FileContent = content

  /** Called when CDT looks for an include while parsing `includer`: `path` is the path CDT asked for, `content` what
    * c2cpg found there (`None`: not found). CDT gets what this returns; `None` leaves the include unresolved. Content a
    * plug-in supplies must be made with `FileContent.create`.
    */
  def includeContent(includer: Path, path: String, content: Option[FileContent]): Option[FileContent] = content

  /** Called while c2cpg reads a parameter, with what CDT parsed for it and its index: a parameter declaration, a K&R
    * parameter's declaration, or a function-style macro's parameter. Returns the (name, value) tags c2cpg puts on the
    * METHOD_PARAMETER_IN it makes from it, wherever it makes it: in the file's AST for a function defined there, or
    * after all files for a function that is only declared (in the file or in a header, the tree's or the system's) and
    * for a macro. Called from several threads at once, like [[onTranslationUnit]].
    */
  def parameterTags(parameter: IASTNode, index: Int): Seq[(String, String)] = Seq.empty

  /** Called for every file c2cpg translates, on the thread that translated it; writes go into `diffGraph`. */
  def onTranslationUnit(unit: TranslationUnitView, diffGraph: DiffGraphBuilder): Unit = ()

}

/** Where c2cpg calls its plug-ins. Loading, failure isolation and the graph pass are x2cpg's
  * ([[io.joern.x2cpg.plugin.FrontendPlugins]]).
  */
object C2CpgPlugin {

  /** The plug-ins of a run, configured and sorted by name: those in `config.plugins` and those on c2cpg's class path
    * that `config.pluginNames` names.
    */
  private[c2cpg] def load(config: Config): Seq[C2CpgPlugin] =
    FrontendPlugins.load(classOf[C2CpgPlugin], config.plugins, config)

  /** `info` passed through every plug-in's [[C2CpgPlugin.scannerInfo]], in name order. */
  private[c2cpg] def scannerInfo(plugins: Seq[C2CpgPlugin], file: Path, info: IScannerInfo): IScannerInfo =
    plugins.foldLeft(info) { (current, plugin) =>
      FrontendPlugins.attempt(plugin, s"the defines and include paths of '$file'", current)(
        plugin.scannerInfo(file, current)
      )
    }

  /** `content` passed through every plug-in's [[C2CpgPlugin.fileContent]], in name order. */
  private[c2cpg] def fileContent(plugins: Seq[C2CpgPlugin], file: Path, content: FileContent): FileContent =
    plugins.foldLeft(content) { (current, plugin) =>
      FrontendPlugins.attempt(plugin, s"the text of '$file'", current)(plugin.fileContent(file, current))
    }

  /** `content` passed through every plug-in's [[C2CpgPlugin.includeContent]], in name order. */
  private[c2cpg] def includeContent(
    plugins: Seq[C2CpgPlugin],
    includer: Path,
    path: String,
    content: Option[FileContent]
  ): Option[FileContent] =
    plugins.foldLeft(content) { (current, plugin) =>
      FrontendPlugins.attempt(plugin, s"the include '$path' of '$includer'", current)(
        plugin.includeContent(includer, path, current)
      )
    }

  /** Every plug-in's [[C2CpgPlugin.parameterTags]] for `parameter`, in name order; none from one that throws. */
  private[c2cpg] def parameterTags(plugins: Seq[C2CpgPlugin], parameter: IASTNode, index: Int): Seq[(String, String)] =
    plugins.flatMap { plugin =>
      FrontendPlugins.attempt(plugin, s"parameter $index '${parameter.getRawSignature}'", Seq.empty[(String, String)])(
        plugin.parameterTags(parameter, index)
      )
    }

  /** The tags `tags` on `parameter`: a TAG node each and a TAGGED_BY edge from the parameter. */
  private[c2cpg] def storeParameterTags(
    parameter: NewNode,
    tags: Seq[(String, String)],
    diffGraph: DiffGraphBuilder
  ): Unit =
    tags.foreach { case (name, value) =>
      val tag = NewTag().name(name).value(value)
      diffGraph.addNode(tag)
      diffGraph.addEdge(parameter, tag, EdgeTypes.TAGGED_BY)
    }

  /** Runs `plugin` on one translated file and adds its writes to `target`, only if it returns normally. */
  private[c2cpg] def runOnTranslationUnit(
    plugin: C2CpgPlugin,
    unit: TranslationUnitView,
    target: DiffGraphBuilder
  ): Unit =
    FrontendPlugins.runInOwnDiff(plugin, s"'${unit.relativePath}'", target) { builder =>
      plugin.onTranslationUnit(unit, builder)
    }
}

/** One translated file: what CDT parsed and the AST nodes c2cpg made from it.
  *
  * @param relativePath
  *   the file's path relative to the input folder, as c2cpg names it
  * @param translationUnit
  *   CDT's translation unit, with its bindings and preprocessor statements; frozen, to be read only
  * @param isCpp
  *   whether the file was parsed as C++
  * @param nodes
  *   the AST nodes c2cpg made for the file, before they are stored
  */
final class TranslationUnitView private[c2cpg] (
  val relativePath: String,
  val translationUnit: IASTTranslationUnit,
  val isCpp: Boolean,
  val nodes: collection.Seq[NewNode]
) {

  private lazy val bySpan: Map[(Int, Int), Seq[AstNodeNew]] = {
    val spans = mutable.LinkedHashMap.empty[(Int, Int), mutable.ArrayBuffer[AstNodeNew]]
    nodes.foreach {
      case astNode: AstNodeNew =>
        for {
          start <- astNode.offset
          end   <- astNode.offsetEnd
        } spans.getOrElseUpdate((start, end), mutable.ArrayBuffer.empty).addOne(astNode)
      case _ =>
    }
    spans.view.mapValues(_.toSeq).toMap
  }

  /** The nodes whose source span is exactly `[offset, offsetEnd)`, in the order c2cpg made them. Spans are set only
    * when file content is enabled.
    */
  def nodesAt(offset: Int, offsetEnd: Int): Seq[AstNodeNew] = bySpan.getOrElse((offset, offsetEnd), Seq.empty)

  /** The nodes made from `cdtNode`'s source span, when that span lies in this file. */
  def nodesFor(cdtNode: IASTNode): Seq[AstNodeNew] = {
    Option(cdtNode.getFileLocation)
      .filter(location => location.getFileName == translationUnit.getFilePath)
      .map(location => nodesAt(location.getNodeOffset, location.getNodeOffset + location.getNodeLength))
      .getOrElse(Seq.empty)
  }
}
