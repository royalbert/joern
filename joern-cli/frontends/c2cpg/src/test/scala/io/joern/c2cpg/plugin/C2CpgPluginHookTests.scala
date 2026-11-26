package io.joern.c2cpg.plugin

import io.joern.c2cpg.{Config, Main}
import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.joern.x2cpg.X2Cpg
import io.shiftleft.codepropertygraph.generated.{Cpg, DiffGraphBuilder, EdgeTypes}
import io.shiftleft.semanticcpg.language.*

import org.eclipse.cdt.core.dom.ast.IASTNode
import org.eclipse.cdt.core.parser.{FileContent, IScannerInfo, ScannerInfo}

import java.nio.file.Path
import java.util.concurrent.ConcurrentLinkedQueue
import scala.jdk.CollectionConverters.*

/** Records where c2cpg calls it, and what it sees there; writes nothing. */
class RecordingPlugin extends C2CpgPlugin {
  val translationUnits: ConcurrentLinkedQueue[String] = new ConcurrentLinkedQueue[String]()
  val events: ConcurrentLinkedQueue[String]           = new ConcurrentLinkedQueue[String]()
  @volatile var configuredWith: Map[String, String]   = Map.empty
  @volatile var graphCalls: Int                       = 0
  @volatile var cfgEdgesAtGraph: Int                  = -1
  @volatile var methodsAtGraph: Int                   = -1

  override def name: String    = "recording"
  override def version: String = "1"

  override def configure(settings: Map[String, String]): C2CpgPlugin = {
    configuredWith = settings
    events.add("configure")
    this
  }

  override def onTranslationUnit(unit: TranslationUnitView, diffGraph: DiffGraphBuilder): Unit = {
    if (unit.translationUnit != null && unit.nodes.nonEmpty) translationUnits.add(unit.relativePath)
    events.add("translationUnit")
  }

  override def onGraph(cpg: Cpg, diffGraph: DiffGraphBuilder): Unit = {
    graphCalls += 1
    cfgEdgesAtGraph = cpg.graph.allEdges.count(_.label == EdgeTypes.CFG)
    methodsAtGraph = cpg.method.size
    events.add("graph")
  }
}

/** Changes CDT's input, and records where c2cpg asked it to: adds a define, supplies a header c2cpg cannot find, and
  * appends a function to the source text.
  */
class InputPlugin(failing: Boolean = false) extends C2CpgPlugin {
  val scannerInfoFiles: ConcurrentLinkedQueue[String] = new ConcurrentLinkedQueue[String]()
  val contentFiles: ConcurrentLinkedQueue[String]     = new ConcurrentLinkedQueue[String]()
  val includes: ConcurrentLinkedQueue[String]         = new ConcurrentLinkedQueue[String]()

  override def name: String    = "input"
  override def version: String = "1"

  override def scannerInfo(file: Path, info: IScannerInfo): IScannerInfo = {
    scannerInfoFiles.add(file.getFileName.toString)
    if (failing) throw new IllegalStateException("test input failure")
    val defines = new java.util.HashMap[String, String](info.getDefinedSymbols)
    defines.put("FROM_PLUGIN", "1")
    new ScannerInfo(defines, info.getIncludePaths)
  }

  override def fileContent(file: Path, content: FileContent): FileContent = {
    contentFiles.add(file.getFileName.toString)
    if (failing) throw new IllegalStateException("test input failure")
    val text = java.nio.file.Files.readString(file)
    FileContent.create(file.toString, true, (text + "\nint appended(void) { return 0; }\n").toCharArray)
  }

  override def includeContent(includer: Path, path: String, content: Option[FileContent]): Option[FileContent] = {
    includes.add(Path.of(path).getFileName.toString)
    if (failing) throw new IllegalStateException("test input failure")
    if (content.isEmpty && path.endsWith("vendor.h")) {
      Some(FileContent.create(path, false, "#define VENDOR_VALUE 42\n".toCharArray))
    } else {
      content
    }
  }
}

/** Answers each parameter c2cpg reads with one tag naming the CDT node it was given and the index. */
class ParameterPlugin(failing: Boolean = false) extends C2CpgPlugin {
  override def name: String    = "parameters"
  override def version: String = "1"

  override def parameterTags(parameter: IASTNode, index: Int): Seq[(String, String)] = {
    if (failing) throw new IllegalStateException("test parameter failure")
    Seq("seen" -> s"${parameter.getClass.getSimpleName}#$index")
  }
}

/** Hook 1 alone: c2cpg runs a plug-in's code once per translated file and once on the graph before any overlay. */
/** A plug-in on c2cpg's test class path (`META-INF/services/io.joern.c2cpg.plugin.C2CpgPlugin`). */
class ClassPathTagPlugin extends C2CpgPlugin {
  override def name: String                                                          = "class-path-tags"
  override def version: String                                                       = "1"
  override def parameterTags(parameter: IASTNode, index: Int): Seq[(String, String)] = Seq("class-path" -> "yes")
}

class C2CpgPluginHookTests extends C2CpgSuite {

  "a c2cpg plug-in" should {
    val plugin = new RecordingPlugin
    val cpg    = code("int f(int x) { return x + 1; }", "main.c")
      .moreCode("int g(void);", "lib.h")
      .withConfig(Config().withPlugins(Seq(plugin)).withPluginSetting("recording", "key", "value"))

    "be configured once, with its settings, before any file" in {
      cpg.method.size should be > 0
      plugin.configuredWith shouldBe Map("key" -> "value")
      plugin.events.asScala.headOption shouldBe Some("configure")
      plugin.events.asScala.count(_ == "configure") shouldBe 1
    }

    "run for every translated file, with CDT's unit and c2cpg's nodes for it" in {
      plugin.translationUnits.asScala.toList.sorted shouldBe List("lib.h", "main.c")
    }

    "run once on the whole graph, after every file and before any overlay" in {
      plugin.graphCalls shouldBe 1
      plugin.events.asScala.last shouldBe "graph"
      plugin.methodsAtGraph should be > 0
      plugin.cfgEdgesAtGraph shouldBe 0
      cpg.graph.allEdges.count(_.label == EdgeTypes.CFG) should be > 0
    }
  }

  "a c2cpg plug-in on CDT's input" should {
    val source = """
        |#include "vendor.h"
        |#if FROM_PLUGIN
        |int gated(void) { return VENDOR_VALUE; }
        |#endif
        |""".stripMargin
    val plugin = new InputPlugin
    val cpg    = code(source, "main.c").withConfig(Config().withPlugins(Seq(plugin)))

    "be asked for each file's defines and include paths, and CDT gets what it returns" in {
      cpg.method.nameExact("gated").size shouldBe 1
      plugin.scannerInfoFiles.asScala.toList should contain("main.c")
    }

    "be asked for each file's text, and CDT parses what it returns" in {
      cpg.method.nameExact("appended").size shouldBe 1
      plugin.contentFiles.asScala.toList should contain("main.c")
    }

    "be asked for each include, and CDT gets the content it returns" in {
      plugin.includes.asScala.toList should contain("vendor.h")
      cpg.literal.code.l should contain("42")
    }
  }

  "a c2cpg plug-in asked for parameter tags" should {
    val source = """
        |#define TWICE(v) ((v) * 2)
        |int defined(int x) { return TWICE(x); }
        |int declared(long y);
        |int knr(a) int a; { return a; }
        |""".stripMargin
    val cpg = code(source, "main.c")
      .moreCode("int in_header(char *z);", "lib.h")
      .withConfig(Config().withPlugins(Seq(new ParameterPlugin)))

    def seen(method: String): List[String] =
      cpg.method.nameExact(method).parameter.l.sortBy(_.index).flatMap(_.tag.nameExact("seen").value.l)

    "run for a defined function's parameters, and its tags are on them" in {
      seen("defined") shouldBe List("CASTParameterDeclaration#1")
    }

    "run for a function only declared, in the file or in a header" in {
      seen("declared") shouldBe List("CASTParameterDeclaration#1")
      seen("in_header") shouldBe List("CASTParameterDeclaration#1")
    }

    "run for a K&R parameter and a macro's parameter" in {
      seen("knr") shouldBe List("CASTSimpleDeclaration#1")
      seen("TWICE") shouldBe List("ASTMacroParameter#1")
    }
  }

  "a c2cpg plug-in that fails on a parameter" should {
    val cpg = code("int kept(int x) { return x; }", "main.c")
      .withConfig(Config().withPlugins(Seq(new ParameterPlugin(failing = true))))

    "leave the parameter without its tags and c2cpg's graph in place" in {
      cpg.method.nameExact("kept").parameter.name.l shouldBe List("x")
      cpg.tag.nameExact("seen") shouldBe empty
    }
  }

  "c2cpg's plug-in options" should {
    "name plug-ins and give each its settings" in {
      val args = Array("input", "--plugin", "vendor", "--plugin-arg", "vendor.mode=fast")
      X2Cpg.parseCommandLine(args, Main.cmdLineParser, Main.frontend.defaultConfig) match {
        case Some(config: Config) =>
          config.pluginNames shouldBe Seq("vendor")
          config.pluginSettings shouldBe Map("vendor" -> Map("mode" -> "fast"))
        case other => fail(s"not parsed: $other")
      }
    }

    "stop the run on a name no c2cpg plug-in has, saying how to fix it" in {
      val error = the[IllegalArgumentException] thrownBy C2CpgPlugin.load(Config().withPlugin("missing"))
      error.getMessage should (include("--plugin 'missing': no C2CpgPlugin has that name") and
        include("available: class-path-tags") and include("leave out --plugin 'missing'"))
    }
  }

  "a c2cpg plug-in on c2cpg's class path" should {
    val source = "void f(int a) {}"

    "run when it is named" in {
      val cpg = code(source, "named.c").withConfig(Config().withPlugin("class-path-tags"))
      cpg.parameter.nameExact("a").tag.nameExact("class-path").value.l shouldBe List("yes")
    }

    "not run when it is not named" in {
      val cpg = code(source, "unnamed.c")
      cpg.parameter.nameExact("a").tag.nameExact("class-path") shouldBe empty
    }
  }

  "a c2cpg plug-in that fails on CDT's input" should {
    val plugin = new InputPlugin(failing = true)
    val cpg    = code("int kept(void) { return 0; }", "main.c").withConfig(Config().withPlugins(Seq(plugin)))

    "leave c2cpg's own input in place" in {
      cpg.method.nameExact("kept").size shouldBe 1
      cpg.method.nameExact("appended") shouldBe empty
      plugin.scannerInfoFiles.asScala.toList should contain("main.c")
    }
  }
}
