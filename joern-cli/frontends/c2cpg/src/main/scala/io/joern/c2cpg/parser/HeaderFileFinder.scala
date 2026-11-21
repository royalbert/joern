package io.joern.c2cpg.parser

import io.joern.c2cpg.C2Cpg.DefaultIgnoredFolders
import io.joern.c2cpg.Config
import io.joern.x2cpg.SourceFiles
import io.shiftleft.semanticcpg.utils.FileUtil.*
import org.jline.utils.Levenshtein

import java.nio.file.Paths
import java.util.concurrent.ConcurrentHashMap

class HeaderFileFinder(config: Config) {

  private val nameToPathMap: Map[String, List[String]] = SourceFiles
    .determine(
      config.inputPath,
      FileDefaults.HeaderFileExtensions,
      ignoredDefaultRegex = Option(DefaultIgnoredFolders),
      ignoredFilesRegex = Option(config.ignoredFilesRegex),
      ignoredFilesPath = Option(config.ignoredFiles)
    )
    .map(path => Paths.get(path))
    .groupMap(_.fileName)(_.toString)

  private val findCache = new ConcurrentHashMap[String, Option[String]]()

  /** The header [[find]] returned for the unresolved `path`, if it did. CDT reads that header under `path`, so the
    * locations of its nodes carry `path`, while the header's own parse carries the header's path.
    */
  private[c2cpg] def substitutedFor(path: String): Option[String] = Option(findCache.get(path)).flatten

  /** Given an unresolved header file, given as a non-existing absolute path, determine whether a header file with the
    * same name can be found anywhere in the code base.
    */
  def find(path: String): Option[String] = findCache.computeIfAbsent(
    path,
    unresolvedPath =>
      Paths.get(unresolvedPath).nameOption.flatMap { name =>
        nameToPathMap.getOrElse(name, List()) match {
          case Nil           => None
          case single :: Nil => Some(single)
          case matches       => matches.minByOption(candidate => Levenshtein.distance(candidate, unresolvedPath))
        }
      }
  )

}
