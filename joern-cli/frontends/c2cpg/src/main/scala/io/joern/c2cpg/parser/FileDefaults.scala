package io.joern.c2cpg.parser

import org.apache.commons.lang3.StringUtils

object FileDefaults {

  val CExt: String            = ".c"
  val CppExt: String          = ".cpp"
  val PreprocessedExt: String = ".i"

  val CHeaderFileExtension: String = ".h"

  val CppHeaderFileExtensions: Set[String] =
    Set(".hpp", ".hh", ".hp", ".hxx", ".h++", ".tcc")

  val HeaderFileExtensions: Set[String] =
    CppHeaderFileExtensions ++ Set(CHeaderFileExtension)

  private val CppSourceFileExtensions: Set[String] =
    Set(".cc", ".cxx", ".cpp", ".cp", ".ccm", ".cxxm", ".c++m")

  val CppFileExtensions: Set[String] =
    CppSourceFileExtensions ++ CppHeaderFileExtensions

  val SourceFileExtensions: Set[String] =
    CppSourceFileExtensions ++ Set(CExt)

  /** As with gcc and clang, an upper-case `.C` file is C++ and only a lower-case `.c` file is C. */
  private val UpperCaseCppExt: String = ".C"

  def hasCppFileExtension(filePath: String): Boolean =
    filePath.endsWith(UpperCaseCppExt) || CppFileExtensions.exists(ext => StringUtils.endsWithIgnoreCase(filePath, ext))

  def hasPreprocessedFileExtension(filePath: String): Boolean =
    StringUtils.endsWithIgnoreCase(filePath, PreprocessedExt)

  def hasCHeaderFileExtension(filePath: String): Boolean =
    StringUtils.endsWithIgnoreCase(filePath, CHeaderFileExtension)

  def hasCFileExtension(filePath: String): Boolean =
    filePath.endsWith(CExt)

}
