package io.joern.joerncli

import io.joern.console.testing.InProcessCpgGenerator
import io.joern.dataflowengineoss.passes.reachingdef.{ArgumentDecision, ArgumentEffect, DefinitionRule}
import io.joern.dataflowengineoss.plugin.DataFlowPlugin
import io.joern.dataflowengineoss.semanticsloader.FlowSemantic
import io.joern.joerncli.JoernParse.ParserConfig
import io.shiftleft.codepropertygraph.generated.{Cpg, EdgeTypes, Languages}
import io.shiftleft.codepropertygraph.generated.nodes.{Call, Expression, Method}
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.utils.FileUtil
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpec

import java.nio.file.Paths
import java.util.concurrent.atomic.AtomicInteger
import scala.util.{Failure, Success}

/** A rule that answers `decision` for the argument of a call to `touch`, and passes other arguments on unchanged. */
class TouchRule(decision: ArgumentDecision) extends DefinitionRule {
  override def appliesTo(cpg: Cpg): Boolean                                      = true
  override def forMethod(method: Method): Call => Expression => ArgumentDecision =
    call => _ => if (call.name == "touch") decision else ArgumentDecision.PassOn
}

/** A plug-in whose rule answers `decision` for `touch`'s argument. Registered in this module's test resources. */
abstract class TouchPlugin(override val name: String, decision: ArgumentDecision) extends DataFlowPlugin {
  override val definitionRule: Option[DefinitionRule] = Some(new TouchRule(decision))
}

/** Not passed on, so Joern's default does not run: each combination of a definition and a cut-off. */
class TouchUntouchedPlugin
    extends TouchPlugin("test-touch-untouched", ArgumentDecision(ArgumentEffect.NoChange, passOn = false))
class TouchMayChangePlugin
    extends TouchPlugin("test-touch-may-change", ArgumentDecision(ArgumentEffect(defines = true), passOn = false))
class TouchEndsPlugin
    extends TouchPlugin("test-touch-ends", ArgumentDecision(ArgumentEffect(cutsOff = true), passOn = false))
class TouchOverwritesPlugin
    extends TouchPlugin("test-touch-overwrites", ArgumentDecision(ArgumentEffect.Overwrites, passOn = false))

/** A tag, passed on, so Joern's default runs too. */
class TouchTaggedPlugin
    extends TouchPlugin(
      "test-touch-tagged",
      ArgumentDecision(ArgumentEffect(tags = Seq("test-clamp" -> "[0, 15]")), passOn = true)
    )

/** A plug-in with semantics only: a call to `touch` passes nothing on. */
class TouchSemanticsPlugin extends DataFlowPlugin {
  override def name: String                  = "test-touch-semantics"
  override def semantics: List[FlowSemantic] = List(FlowSemantic("touch", List.empty))
}

/** Counts the calls the data-flow pass makes to its rule; passes every argument on unchanged. */
object CountingRule extends DefinitionRule {
  val appliesToCalls: AtomicInteger = new AtomicInteger()
  val forMethodCalls: AtomicInteger = new AtomicInteger()
  val ruleCalls: AtomicInteger      = new AtomicInteger()

  def reset(): Unit = Seq(appliesToCalls, forMethodCalls, ruleCalls).foreach(_.set(0))

  override def appliesTo(cpg: Cpg): Boolean = { appliesToCalls.incrementAndGet(); true }
  override def forMethod(method: Method): Call => Expression => ArgumentDecision = {
    forMethodCalls.incrementAndGet()
    _ => _ => { ruleCalls.incrementAndGet(); ArgumentDecision.PassOn }
  }
}

class CountingPlugin extends DataFlowPlugin {
  override def name: String                           = "test-counting"
  override def definitionRule: Option[DefinitionRule] = Some(CountingRule)
}

/** A plug-in whose rule fails when the pass asks whether it applies. */
class FailingPlugin extends DataFlowPlugin {
  override def name: String                           = "test-failing"
  override def definitionRule: Option[DefinitionRule] = Some(new DefinitionRule {
    override def appliesTo(cpg: Cpg): Boolean = throw new IllegalStateException("test rule failure")
    override def forMethod(method: Method): Call => Expression => ArgumentDecision = _ => _ => ArgumentDecision.PassOn
  })
}

class JoernParseDataFlowPluginTests extends AnyWordSpec with Matchers {

  private def testCode(name: String) = Paths.get(getClass.getClassLoader.getResource(s"testcode/$name").toURI).toString

  /** joern-parse's overlay stage, through its own argument parsing, on the test code's frontend graph. */
  private def parseWithOverlays[T](code: String, arguments: Seq[String])(
    check: (scala.util.Try[String], String) => T
  ): T = {
    FileUtil.usingTemporaryDirectory("joern-parse-data-flow-plugin-test") { tmpDir =>
      val cpgPath = tmpDir.resolve("cpg.bin").toString
      InProcessCpgGenerator.c().generate(inputPath = testCode(code), outputPath = cpgPath).get
      val config = JoernParse.optionParser
        .parse(
          Seq(cpgPath, "--output", cpgPath, "--language", Languages.NEWC, "--overlaysonly") ++ arguments,
          ParserConfig()
        )
        .getOrElse(fail(s"joern-parse did not parse ${arguments.mkString(" ")}"))
      check(JoernParse.run(config), cpgPath)
    }
  }

  /** The graph joern-parse stores with `arguments`, given to `read`. */
  private def stored[T](code: String, arguments: Seq[String])(read: Cpg => T): T =
    parseWithOverlays(code, arguments) { (result, cpgPath) =>
      result match {
        case Failure(exception) => fail(s"joern-parse ${arguments.mkString(" ")} failed", exception)
        case Success(_)         =>
          val cpg = CpgBasedTool.loadFromFile(cpgPath)
          try { read(cpg) }
          finally { cpg.close() }
      }
    }

  /** The code of the definitions that reach `x` in `use(x)`, sorted; the method node, which Joern links to every use,
    * is left out.
    */
  private def reachingUse(arguments: Seq[String]): List[String] =
    stored("effects", arguments) { cpg =>
      cpg.call
        .nameExact("use")
        .argument
        .isIdentifier
        .nameExact("x")
        .l
        .flatMap(_._reachingDefIn)
        .collect {
          case call: Call        => call.code
          case other: Expression => s"${other.inCall.code.headOption.getOrElse("")}: ${other.code}"
        }
        .sorted
    }

  private def reachingDefEdges(code: String, arguments: Seq[String]): Int =
    stored(code, arguments)(_.graph.allEdges.count(_.label == EdgeTypes.REACHING_DEF))

  private def causeMessages(exception: Throwable): String =
    Iterator.iterate(exception)(_.getCause).takeWhile(_ != null).map(_.getMessage).mkString(" / ")

  private def plugins(names: String*): Seq[String] = names.flatMap(name => Seq("--data-flow-plugin", name))

  "joern-parse --data-flow-plugin" should {
    "take each named plug-in, in order" in {
      JoernParse.optionParser
        .parse(Seq("in") ++ plugins("first", "second"), ParserConfig())
        .map(_.dataFlowPlugins) shouldBe Some(Seq("first", "second"))
    }

    "find a plug-in by its name on the class path" in {
      PluginProviders.dataFlowPlugins(Seq("test-touch-ends")).map(_.getClass) shouldBe Seq(classOf[TouchEndsPlugin])
    }

    "ask a named plug-in's rule in the data flow calculation, and change nothing where it passes on unchanged" in {
      CountingRule.reset()
      val withCounting = reachingDefEdges("free", plugins("test-counting"))
      CountingRule.appliesToCalls.get shouldBe 1
      CountingRule.forMethodCalls.get should be > 0
      CountingRule.ruleCalls.get should be > 0
      withCounting shouldBe reachingDefEdges("free", Seq.empty)
    }

    "let a rule that does not pass an argument on decide whether the call defines it and cuts off earlier definitions" in {
      reachingUse(Seq.empty) shouldBe List("touch(x): x")
      reachingUse(plugins("test-touch-overwrites")) shouldBe List("touch(x): x")
      reachingUse(plugins("test-touch-untouched")) shouldBe List("x = a: x")
      reachingUse(plugins("test-touch-may-change")) shouldBe List("touch(x): x", "x = a: x")
      reachingUse(plugins("test-touch-ends")) shouldBe empty
    }

    "keep Joern's default for an argument a rule passes on, together with the rule's changes" in {
      stored("effects", plugins("test-touch-tagged")) { cpg =>
        cpg.call.nameExact("touch").argument.tag.nameExact("test-clamp").value.l shouldBe List("[0, 15]")
        cpg.call.nameExact("use").argument.tag.nameExact("test-clamp") shouldBe empty
      }
      reachingUse(plugins("test-touch-tagged")) shouldBe List("touch(x): x")
    }

    "ask the rules in the order the plug-ins are named, up to the first that does not pass the argument on" in {
      reachingUse(plugins("test-touch-untouched", "test-touch-ends")) shouldBe List("x = a: x")
      reachingUse(plugins("test-touch-ends", "test-touch-untouched")) shouldBe empty
      reachingUse(plugins("test-counting", "test-touch-untouched")) shouldBe List("x = a: x")
      reachingUse(plugins("test-touch-tagged", "test-touch-ends")) shouldBe empty
      stored("effects", plugins("test-touch-tagged", "test-touch-ends")) { cpg =>
        cpg.call.nameExact("touch").argument.tag.nameExact("test-clamp").value.l shouldBe List("[0, 15]")
      }
      stored("effects", plugins("test-touch-ends", "test-touch-tagged")) { cpg =>
        cpg.call.nameExact("touch").argument.tag.nameExact("test-clamp") shouldBe empty
      }
    }

    "add a plug-in's semantics to the default ones" in {
      val default   = reachingDefEdges("effects", Seq.empty)
      val semantics = reachingDefEdges("effects", plugins("test-touch-semantics"))
      info(s"REACHING_DEF edges: default $default, with the plug-in's semantics $semantics")
      semantics should not be default
    }

    "fail before any graph is built when the overlays that run the plug-in are turned off" in {
      val config =
        ParserConfig(inputPath = testCode("free"), dataFlowPlugins = Seq("test-touch-ends"), enhance = false)
      JoernParse.run(config) match {
        case Failure(exception) =>
          exception.getMessage should (include("--data-flow-plugin 'test-touch-ends': these run with the overlays") and
            include("Leave out --nooverlays"))
        case Success(_) => fail("joern-parse ran a data-flow plug-in with the overlays off")
      }
    }

    "fail before any graph is built when no plug-in has the name" in {
      val config = ParserConfig(inputPath = testCode("free"), dataFlowPlugins = Seq("no-such-plugin"))
      JoernParse.run(config) match {
        case Failure(exception) =>
          exception.getMessage should (include(
            "--data-flow-plugin 'no-such-plugin': no data-flow plug-in has that name"
          ) and include("leave out --data-flow-plugin 'no-such-plugin'"))
        case Success(_) => fail("joern-parse ran with an unknown data-flow plug-in")
      }
    }

    "fail the run when a plug-in fails" in {
      parseWithOverlays("free", plugins("test-failing")) { (result, _) =>
        result match {
          case Failure(exception) =>
            causeMessages(exception) should include("test rule failure")
            causeMessages(exception) should (include("--data-flow-plugin 'test-failing': the plug-in failed") and
              include("leave out --data-flow-plugin 'test-failing'"))
          case Success(_) => fail("joern-parse succeeded with a failing data-flow plug-in")
        }
      }
    }
  }
}
