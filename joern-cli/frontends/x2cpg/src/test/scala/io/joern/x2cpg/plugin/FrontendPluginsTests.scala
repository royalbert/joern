package io.joern.x2cpg.plugin

import io.joern.x2cpg.{X2Cpg, X2CpgConfig}
import io.shiftleft.codepropertygraph.generated.{Cpg, DiffGraphBuilder}
import io.shiftleft.codepropertygraph.generated.nodes.NewFile
import io.shiftleft.semanticcpg.language.*
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpec

/** A frontend's configuration with nothing of its own, as a frontend that offers plug-ins would have. */
final case class TestFrontendConfig(override val genericConfig: X2CpgConfig.GenericConfig = X2CpgConfig.GenericConfig())
    extends X2CpgConfig[TestFrontendConfig] {
  override def withGenericConfig(value: X2CpgConfig.GenericConfig): TestFrontendConfig = copy(genericConfig = value)
}

/** A frontend's own plug-in kind, with one call of its own. */
trait TestFrontendPlugin extends FrontendPlugin {
  def onFile(file: String, diffGraph: DiffGraphBuilder): Unit = ()
}

/** Records its settings, and adds a FILE node from `onGraph` unless told to fail there. */
class RecordingFrontendPlugin(override val name: String, failing: Boolean = false) extends TestFrontendPlugin {
  override def version: String                              = "1"
  @volatile var configuredWith: Option[Map[String, String]] = None

  override def configure(settings: Map[String, String]): TestFrontendPlugin = {
    configuredWith = Some(settings)
    this
  }

  override def onGraph(cpg: Cpg, diffGraph: DiffGraphBuilder): Unit = {
    diffGraph.addNode(NewFile().name(s"from-$name"))
    if (failing) throw new IllegalStateException("test graph failure")
  }
}

/** A plug-in on the test class path (`META-INF/services/io.joern.x2cpg.plugin.TestFrontendPlugin`). */
class ClassPathPlugin extends TestFrontendPlugin {
  override def name: String                                 = "class-path"
  override def version: String                              = "1"
  @volatile var configuredWith: Option[Map[String, String]] = None

  override def configure(settings: Map[String, String]): TestFrontendPlugin = {
    configuredWith = Some(settings)
    this
  }
}

/** Two plug-ins on the test class path with the same name. */
class TwinPlugin extends TestFrontendPlugin {
  override def name: String    = "twin"
  override def version: String = "1"
}

class OtherTwinPlugin extends TwinPlugin

class FrontendPluginsTests extends AnyWordSpec with Matchers {

  private val kind = classOf[TestFrontendPlugin]

  "loading a frontend's plug-ins" should {
    "configure each, with its own settings, and sort them by name" in {
      val second = new RecordingFrontendPlugin("second")
      val first  = new RecordingFrontendPlugin("first")
      val config = TestFrontendConfig().withPluginSetting("first", "mode", "fast")
      FrontendPlugins.load(kind, Seq(second, first), config).map(_.name) shouldBe Seq("first", "second")
      first.configuredWith shouldBe Some(Map("mode" -> "fast"))
      second.configuredWith shouldBe Some(Map.empty)
    }

    "refuse an invalid or a duplicate name, saying how to fix it" in {
      val invalid = the[IllegalArgumentException] thrownBy {
        FrontendPlugins.load(kind, Seq(new RecordingFrontendPlugin("bad name")), TestFrontendConfig())
      }
      invalid.getMessage should (include("Plug-in 'bad name'") and include("letters, digits, - and _"))
      val twice     = Seq(new RecordingFrontendPlugin("same"), new RecordingFrontendPlugin("same"))
      val duplicate = the[IllegalArgumentException] thrownBy FrontendPlugins.load(kind, twice, TestFrontendConfig())
      duplicate.getMessage should (include("More than one plug-in is named 'same'") and include(
        "Leave out all but one"
      ))
    }

    "run a plug-in from the class path only when it is named, configured with its settings" in {
      val config  = TestFrontendConfig().withPlugin("class-path").withPluginSetting("class-path", "mode", "fast")
      val plugins = FrontendPlugins.load(kind, Seq.empty, config)
      plugins.map(_.name) shouldBe Seq("class-path")
      plugins.collect { case plugin: ClassPathPlugin => plugin.configuredWith } shouldBe Seq(
        Some(Map("mode" -> "fast"))
      )
    }

    "not search the class path when no plug-in is named" in {
      val refusing = new ClassLoader(getClass.getClassLoader) {
        override def getResources(name: String): java.util.Enumeration[java.net.URL] =
          throw new IllegalStateException(s"searched for $name")
      }
      FrontendPlugins.load(kind, Seq.empty, TestFrontendConfig(), refusing) shouldBe empty
    }

    "fail on a name no plug-in has, saying how to fix it" in {
      val error = the[IllegalArgumentException] thrownBy {
        FrontendPlugins.load(kind, Seq.empty, TestFrontendConfig().withPlugin("missing"))
      }
      error.getMessage should (include("--plugin 'missing': no TestFrontendPlugin has that name") and
        include("available: class-path, twin, twin") and include("leave out --plugin 'missing'"))
    }

    "fail on a name two plug-ins on the class path have, saying how to fix it" in {
      val error = the[IllegalArgumentException] thrownBy {
        FrontendPlugins.load(kind, Seq.empty, TestFrontendConfig().withPlugin("twin"))
      }
      error.getMessage should (include("--plugin 'twin': more than one plug-in jar") and include("Remove all but one"))
    }
  }

  "a frontend's plug-in options" should {
    "name plug-ins and give each its settings" in {
      val parser = FrontendPlugins.commandLineOptions[TestFrontendConfig]("TestFrontendPlugin")
      val args   = Array("input", "--plugin", "vendor", "--plugin-arg", "vendor.mode=fast")
      X2Cpg.parseCommandLine(args, parser, TestFrontendConfig()) match {
        case Some(config) =>
          config.pluginNames shouldBe Seq("vendor")
          config.pluginSettings shouldBe Map("vendor" -> Map("mode" -> "fast"))
          config.withoutNamedPlugins.pluginNames shouldBe empty
        case None => fail("not parsed")
      }
    }

    "refuse a setting that is not <name>.<key>=<value>" in {
      val parser = FrontendPlugins.commandLineOptions[TestFrontendConfig]("TestFrontendPlugin")
      X2Cpg.parseCommandLine(Array("input", "--plugin-arg", "nokey"), parser, TestFrontendConfig()) shouldBe None
    }
  }

  "the graph pass" should {
    "run every plug-in's onGraph, and drop only a failing plug-in's writes" in {
      val cpg     = X2Cpg.newEmptyCpg(None)
      val plugins =
        Seq(new RecordingFrontendPlugin("kept"), new RecordingFrontendPlugin("lost", failing = true))
      new FrontendPlugins.GraphPass(cpg, plugins).createAndApply()
      cpg.file.name.l shouldBe List("from-kept")
      cpg.close()
    }
  }

  "a plug-in's call that throws" should {
    "leave the frontend's own value in place" in {
      val plugin = new RecordingFrontendPlugin("throwing")
      FrontendPlugins.attempt(plugin, "a test value", "unchanged")(throw new IllegalStateException("boom")) shouldBe
        "unchanged"
    }
  }
}
