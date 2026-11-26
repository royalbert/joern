package io.joern.joerncli

import io.joern.dataflowengineoss.layers.dataflows.OssDataFlow
import io.joern.joerncli.JoernParse.ParserConfig
import io.joern.x2cpg.layers.CallGraph
import io.joern.x2cpg.passes.frontend.MetaDataPass
import io.shiftleft.codepropertygraph.generated.{Cpg, Languages}
import io.shiftleft.semanticcpg.Overlays
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.layers.{LayerCreator, LayerCreatorContext, LayerCreatorProvider}
import io.shiftleft.semanticcpg.utils.FileUtil
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpec

import scala.util.{Failure, Success}

/** Where joern-parse ran the test layers, and what each saw then: its name and the overlays already applied. */
object LayerRuns {
  private val runs = scala.collection.mutable.ArrayBuffer.empty[(String, List[String])]
  def record(name: String, applied: Seq[String]): Unit = synchronized { runs.addOne((name, applied.toList)) }
  def all: List[(String, List[String])]                = synchronized { runs.toList }
  def reset(): Unit                                    = synchronized { runs.clear() }
}

/** A vendor layer that runs after the data flow overlay and records that it ran; writes nothing. */
class TestVendorLayer extends LayerCreator {
  override val overlayName: String     = "testVendorLayer"
  override val description: String     = "records that it ran, after the data flow overlay"
  override val dependsOn: List[String] = List(CallGraph.overlayName, OssDataFlow.overlayName)

  override def create(context: LayerCreatorContext): Unit =
    LayerRuns.record(overlayName, Overlays.appliedOverlays(context.cpg))
}

class TestVendorLayerProvider extends LayerCreatorProvider {
  override def name: String                 = "test-vendor-layer"
  override def last(): Option[LayerCreator] = Some(new TestVendorLayer)
}

/** A layer that depends on a layer no graph has. */
class TestLayerWithMissingDependencyProvider extends LayerCreatorProvider {
  override def name: String                 = "test-missing-dependency"
  override def last(): Option[LayerCreator] = Some(new LayerCreator {
    override val overlayName: String                        = "testMissingDependency"
    override val description: String                        = "depends on a layer that does not exist"
    override val dependsOn: List[String]                    = List("noSuchLayer")
    override def create(context: LayerCreatorContext): Unit = ()
  })
}

/** A layer that records that it ran, so that the order layers ran in can be read back. */
class RecordingLayer(layerName: String, dependencies: List[String]) extends LayerCreator {
  override val overlayName: String     = layerName
  override val description: String     = s"records $layerName"
  override val dependsOn: List[String] = dependencies

  override def create(context: LayerCreatorContext): Unit =
    LayerRuns.record(layerName, Overlays.appliedOverlays(context.cpg))
}

class TestFirstLayerProvider extends LayerCreatorProvider {
  override def name: String                 = "test-first"
  override def last(): Option[LayerCreator] = Some(new RecordingLayer("testFirst", List(CallGraph.overlayName)))
}

class TestSecondLayerProvider extends LayerCreatorProvider {
  override def name: String                 = "test-second"
  override def last(): Option[LayerCreator] = Some(new RecordingLayer("testSecond", List("testFirst")))
}

class TestCycleLayerProvider extends LayerCreatorProvider {
  override def name: String                 = "test-cycle"
  override def last(): Option[LayerCreator] = Some(new RecordingLayer("testCycle", List("testCycleOther")))
}

class TestCycleOtherLayerProvider extends LayerCreatorProvider {
  override def name: String                 = "test-cycle-other"
  override def last(): Option[LayerCreator] = Some(new RecordingLayer("testCycleOther", List("testCycle")))
}

/** A layer that throws while it runs. */
class TestFailingLayerProvider extends LayerCreatorProvider {
  override def name: String                 = "test-failing-layer"
  override def last(): Option[LayerCreator] = Some(new LayerCreator {
    override val overlayName: String                        = "testFailingLayer"
    override val description: String                        = "throws"
    override def create(context: LayerCreatorContext): Unit = throw new IllegalStateException("test layer failure")
  })
}

/** Gives a layer to run first, before the default overlays, and one to run last, after them. */
class TestBothEndsLayerProvider extends LayerCreatorProvider {
  override def name: String                  = "test-both-ends"
  override def first(): Option[LayerCreator] = Some(new RecordingLayer("testBothFirst", Nil))
  override def last(): Option[LayerCreator]  = Some(new RecordingLayer("testBothLast", List(OssDataFlow.overlayName)))
}

/** Gives no layer at all. */
class TestNoLayerProvider extends LayerCreatorProvider {
  override def name: String = "test-no-layer"
}

class JoernParseLayerTests extends AnyWordSpec with Matchers {

  private def layerArguments(names: String*): Seq[String] = names.flatMap(name => Seq("--layer", name))

  /** Runs joern-parse's overlay stage on a graph with only a META_DATA node, with `layers`. */
  private def runOverlays[T](layers: Seq[String])(check: (scala.util.Try[String], java.nio.file.Path) => T): T = {
    FileUtil.usingTemporaryDirectory("joern-parse-layer-test") { tmpDir =>
      val cpgPath = tmpDir.resolve("cpg.bin")
      val cpg     = Cpg.withStorage(cpgPath)
      new MetaDataPass(cpg, Languages.PHP, tmpDir.toString).createAndApply()
      cpg.close()
      val arguments = Seq(cpgPath.toString, "--output", cpgPath.toString, "--language", "php", "--overlaysonly")
      val config    = JoernParse.optionParser
        .parse(arguments ++ layerArguments(layers*), ParserConfig())
        .getOrElse(fail(s"joern-parse did not parse --layer ${layers.mkString(" ")}"))
      check(JoernParse.run(config), cpgPath)
    }
  }

  "joern-parse --layer" should {
    "run a named layer's code once, alone, after the default overlays and the data flow overlay" in {
      LayerRuns.reset()
      runOverlays(Seq("test-vendor-layer")) { (result, cpgPath) =>
        result match {
          case Failure(exception) => fail("joern-parse --layer failed", exception)
          case Success(_)         =>
            LayerRuns.all.map(_._1) shouldBe List("testVendorLayer")
            LayerRuns.all.head._2 should contain.allOf(CallGraph.overlayName, OssDataFlow.overlayName)
            val cpg = CpgBasedTool.loadFromFile(cpgPath.toString)
            try { cpg.metaData.overlays.l.last shouldBe "testVendorLayer" }
            finally { cpg.close() }
        }
      }
    }

    "fail when the named layer depends on a layer the graph does not have" in {
      runOverlays(Seq("test-missing-dependency")) { (result, _) =>
        result match {
          case Failure(exception) =>
            exception.getMessage should (include("depends on noSuchLayer") and include(
              "leave out --layer 'test-missing-dependency'"
            ))
          case Success(_) => fail("joern-parse ran a layer whose dependency is missing")
        }
      }
    }

    "fail when no layer has the name" in {
      runOverlays(Seq("no-such-layer")) { (result, _) =>
        result match {
          case Failure(exception) =>
            exception.getMessage should (include("--layer 'no-such-layer': no layer has that name") and include(
              "leave out --layer 'no-such-layer'"
            ))
          case Success(_) => fail("joern-parse ran with an unknown layer")
        }
      }
    }

    "take each named layer, in order" in {
      JoernParse.optionParser
        .parse(Seq("in") ++ layerArguments("first", "second"), ParserConfig())
        .map(_.layers) shouldBe Some(Seq("first", "second"))
    }

    "run named layers after the layers they depend on, whatever order they are named in" in {
      LayerRuns.reset()
      runOverlays(Seq("test-second", "test-first")) { (result, _) =>
        result match {
          case Failure(exception) => fail("joern-parse --layer failed", exception)
          case Success(_)         => LayerRuns.all.map(_._1) shouldBe List("testFirst", "testSecond")
        }
      }
    }

    "fail before any graph is built when named layers depend on each other in a cycle" in {
      runOverlays(Seq("test-cycle", "test-cycle-other")) { (result, _) =>
        result match {
          case Failure(exception) =>
            exception.getMessage should (include("depend on each other in a cycle") and include(
              "Leave out one of the layers"
            ))
          case Success(_) => fail("joern-parse ran layers that depend on each other")
        }
      }
    }

    "fail the run when a layer fails, and not list that layer as applied" in {
      runOverlays(Seq("test-failing-layer")) { (result, cpgPath) =>
        result match {
          case Failure(exception) =>
            exception.getMessage should include("--layer 'test-failing-layer': the layer failed")
            val cpg = CpgBasedTool.loadFromFile(cpgPath.toString)
            try {
              cpg.metaData.overlays.l should contain(OssDataFlow.overlayName)
              cpg.metaData.overlays.l should not contain "testFailingLayer"
            } finally {
              cpg.close()
            }
          case Success(_) => fail("joern-parse succeeded with a failing layer")
        }
      }
    }

    "run a provider's first layer before the default overlays and its last layer after them" in {
      LayerRuns.reset()
      runOverlays(Seq("test-both-ends")) { (result, cpgPath) =>
        result match {
          case Failure(exception) => fail("joern-parse --layer failed", exception)
          case Success(_)         =>
            LayerRuns.all.map(_._1) shouldBe List("testBothFirst", "testBothLast")
            LayerRuns.all.head._2 shouldBe empty
            LayerRuns.all.last._2 should contain.allOf(CallGraph.overlayName, OssDataFlow.overlayName)
            val cpg = CpgBasedTool.loadFromFile(cpgPath.toString)
            try {
              val overlays = cpg.metaData.overlays.l
              overlays.head shouldBe "testBothFirst"
              overlays.last shouldBe "testBothLast"
            } finally {
              cpg.close()
            }
        }
      }
    }

    "fail before any graph is built when the named provider gives no layer" in {
      runOverlays(Seq("test-no-layer")) { (result, _) =>
        result match {
          case Failure(exception) =>
            exception.getMessage should (include("--layer 'test-no-layer': the plug-in gives no layer") and include(
              "leave out --layer 'test-no-layer'"
            ))
          case Success(_) => fail("joern-parse ran a provider without a layer")
        }
      }
    }

    "find every provider on the class path" in {
      PluginProviders.layerProviders().map(_.name) should contain.allOf("test-missing-dependency", "test-vendor-layer")
    }
  }
}
