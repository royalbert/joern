package io.joern.joerncli

import io.joern.console.cpgcreation.{CpgGenerator, cpgGeneratorForLanguage, guessLanguage}
import io.joern.console.{FrontendConfig, InstallConfig}
import io.joern.dataflowengineoss.plugin.DataFlowPlugin
import io.joern.joerncli.CpgBasedTool.newCpgCreatedString
import io.joern.x2cpg.frontendspecific.FrontendArgsDelimitor
import io.shiftleft.codepropertygraph.generated.{Cpg, Languages}
import io.shiftleft.semanticcpg.Overlays
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.layers.{LayerCreator, LayerCreatorContext, LayerCreatorProvider}

import java.nio.file.{Files, Paths}
import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.util.control.NonFatal
import scala.util.{Failure, Success, Try}

object JoernParse {
  val DefaultCpgOutFile       = "cpg.bin"
  var generator: CpgGenerator = scala.compiletime.uninitialized

  def main(args: Array[String]): Unit = {
    run(args) match {
      case Success(msg) =>
        println(msg)
      case Failure(err) =>
        err.printStackTrace()
        System.exit(1)
    }
  }

  val optionParser = new scopt.OptionParser[ParserConfig]("joern-parse") {
    arg[String]("input")
      .optional()
      .text("source file or directory containing source files")
      .action((x, c) => c.copy(inputPath = x))

    opt[String]('o', "output")
      .text("output filename")
      .action((x, c) => c.copy(outputCpgFile = x))

    opt[String]("language")
      .text("source language")
      .action((x, c) => c.copy(language = x))

    opt[Unit]("list-languages")
      .text("list available language options")
      .action((_, c) => c.copy(listLanguages = true))

    opt[String]("namespaces")
      .text("namespaces to include: comma separated string")
      .action((x, c) => c.copy(namespaces = x.split(",").map(_.trim).toSeq))

    note("Overlay application stage")

    opt[Unit]("nooverlays")
      .text("do not apply default overlays")
      .action((_, c) => c.copy(enhance = false))
    opt[Unit]("overlaysonly")
      .text("Only apply default overlays")
      .action((_, c) => c.copy(enhanceOnly = true))

    opt[Int]("max-num-def")
      .text("Maximum number of definitions in per-method data flow calculation")
      .action((x, c) => c.copy(maxNumDef = x))

    opt[String]("data-flow-plugin")
      .unbounded()
      .text("run the data-flow plug-in with this name in the data flow calculation (a DataFlowPlugin)")
      .action((name, config) => config.copy(dataFlowPlugins = config.dataFlowPlugins :+ name))

    opt[String]("layer")
      .unbounded()
      .text(
        "run the layers with this name (a LayerCreatorProvider) before and after the default overlays; ordered by " +
          "their dependsOn"
      )
      .action((name, config) => config.copy(layers = config.layers :+ name))

    note("Misc")
    help("help").text("display this help message")

    note(s"Args specified after the $FrontendArgsDelimitor separator will be passed to the front-end verbatim")
  }

  private def run(args: Array[String]): Try[String] = {
    val (parserArgs, frontendArgs) = CpgBasedTool.splitArgs(args)
    val installConfig              = new InstallConfig()

    parseConfig(parserArgs).flatMap { config =>
      if (config.listLanguages)
        Try(buildLanguageList())
      else
        run(config, frontendArgs, installConfig)
    }
  }

  def run(
    config: ParserConfig,
    frontendArgs: List[String] = List.empty,
    installConfig: InstallConfig = InstallConfig()
  ): Try[String] = {
    for {
      _               <- checkInputPath(config)
      language        <- getLanguage(config)
      _               <- Try(checkOverlaysFor(config))
      dataFlowPlugins <- Try(PluginProviders.dataFlowPlugins(config.dataFlowPlugins))
      layers          <- Try(checkedLayers(config.layers))
      _               <- generateCpg(installConfig, frontendArgs, config, language)
      _               <- applyDefaultOverlays(config, installConfig, dataFlowPlugins, layers)
    } yield newCpgCreatedString(config.outputCpgFile)
  }

  /** Named data-flow plug-ins and layers run with the overlays; fails before any graph is built when `--nooverlays`
    * would skip them.
    */
  private def checkOverlaysFor(config: ParserConfig): Unit = {
    val named =
      config.dataFlowPlugins.map(name => s"--data-flow-plugin '$name'") ++ config.layers.map(name => s"--layer '$name'")
    if (!config.enhance && named.nonEmpty) {
      throw new IllegalArgumentException(
        s"${named.mkString(", ")}: these run with the overlays, which --nooverlays turns off. Leave out " +
          s"--nooverlays, or leave out ${named.mkString(" and ")} to build without them."
      )
    }
  }

  private def checkInputPath(config: ParserConfig): Try[Unit] = {
    Try {
      if (config.inputPath == "") {
        println(optionParser.usage)
        throw new AssertionError(s"Input path required")
      } else if (!Files.exists(Paths.get(config.inputPath)))
        throw new AssertionError(s"Input path does not exist at `${config.inputPath}`, exiting.")
      else ()
    }
  }

  private def buildLanguageList(): String = {
    val s = new mutable.StringBuilder()
    s ++= "Available languages (case insensitive):\n"
    s ++= Languages.ALL.asScala.map(lang => s"- ${lang.toLowerCase}").mkString("\n")
    s.toString()
  }

  private def getLanguage(config: ParserConfig): Try[String] = {
    Try {
      if (config.language.nonEmpty) {
        config.language
      } else {
        guessLanguage(config.inputPath)
          .getOrElse(
            throw new AssertionError(
              s"Could not guess language from input path ${config.inputPath}. Please specify a language using the --language option."
            )
          )
      }
    }
  }

  private def generateCpg(
    installConfig: InstallConfig,
    frontendArgs: Seq[String],
    config: ParserConfig,
    language: String
  ): Try[String] = {
    if (config.enhanceOnly) {
      Success("No generation required")
    } else {
      println(s"Parsing code at: ${config.inputPath} - language: `$language`")
      println("[+] Running language frontend")
      Try {
        cpgGeneratorForLanguage(language.toUpperCase, FrontendConfig(), installConfig.rootPath, frontendArgs.toList).get
      }.flatMap { newGenerator =>
        generator = newGenerator
        generator
          .generate(config.inputPath, outputPath = config.outputCpgFile)
          .recover { case exception =>
            throw new RuntimeException(
              s"Could not generate CPG with language = $language and input = ${config.inputPath}",
              exception
            )
          }
      }
    }
  }

  private def applyDefaultOverlays(
    config: ParserConfig,
    installConfig: InstallConfig,
    dataFlowPlugins: Seq[DataFlowPlugin],
    layers: Seq[LayerCreatorProvider]
  ): Try[String] = {
    Try {
      println("[+] Applying default overlays")
      if (config.enhance) {
        val cpg =
          try {
            DefaultOverlays.create(
              config.outputCpgFile,
              config.maxNumDef,
              definitionRules = dataFlowPlugins.flatMap(_.definitionRule),
              semantics = dataFlowPlugins.toList.flatMap(_.semantics),
              beforeOverlays = cpg => applyLayers(cpg, PluginProviders.firstLayers(layers), "before")
            )
          } catch {
            case NonFatal(exception) =>
              failingPlugin(dataFlowPlugins, exception) match {
                case Some(name) =>
                  throw new RuntimeException(
                    s"--data-flow-plugin '$name': the plug-in failed (see the cause below). Fix or update the " +
                      s"plug-in jar that provides it, or leave out --data-flow-plugin '$name' to build without it.",
                    exception
                  )
                case None => throw exception
              }
          }
        // With --overlaysonly no frontend ran, so `generator` is unset. Resolve a generator from the
        // CPG's language instead, so language-specific post-processing passes are still applied.
        val postProcessingGenerator = Option(generator).orElse {
          cpg.metaData.language.headOption
            .flatMap(cpgGeneratorForLanguage(_, FrontendConfig(), installConfig.rootPath, args = Nil))
        }
        postProcessingGenerator match {
          case Some(resolvedGenerator) => resolvedGenerator.applyPostProcessingPasses(cpg)
          case None                    =>
            cpg.close()
            throw new RuntimeException(
              s"Could not resolve a language frontend for post-processing passes: the CPG at ${config.outputCpgFile} " +
                "has no metadata node with a known language and appears to be broken."
            )
        }
        try {
          applyLayers(cpg, PluginProviders.lastLayers(layers), "after")
        } finally {
          cpg.close()
        }
      }
      "Code property graph generation successful"
    }
  }

  /** The providers of the named layers; fails, before any graph is built, on an unknown name, a provider without a
    * layer, or a cycle among the layers that run first or among those that run last.
    */
  private def checkedLayers(names: Seq[String]): Seq[LayerCreatorProvider] = {
    val providers = PluginProviders.layers(names)
    PluginProviders.firstLayers(providers)
    PluginProviders.lastLayers(providers)
    providers
  }

  /** The name of the data-flow plug-in whose code `exception` or one of its causes was thrown from, if any. */
  private def failingPlugin(plugins: Seq[DataFlowPlugin], exception: Throwable): Option[String] = {
    val frames =
      Iterator.iterate(exception)(_.getCause).takeWhile(_ != null).flatMap(_.getStackTrace).map(_.getClassName).toSeq
    plugins.collectFirst {
      case plugin
          if (plugin +: plugin.definitionRule.toSeq)
            .exists(code => frames.exists(_.startsWith(code.getClass.getName.stripSuffix("$")))) =>
        plugin.name
    }
  }

  /** Runs `layers` on `cpg`, in the order given, `before` or `after` the default overlays: before them on the
    * frontend's graph, or after the default overlays, the data-flow overlay and the frontend's post-processing passes.
    *
    * A named layer is never skipped: one that depends on a layer the graph does not have, or that was applied before,
    * fails the run before it starts. A layer that throws fails the run too. When a layer that runs after the overlays
    * fails, the stored graph keeps the default overlays and every layer that finished, and does not list the failed
    * layer among its overlays; when one that runs before them fails, the stored graph is the frontend's.
    */
  private def applyLayers(cpg: Cpg, layers: Seq[(LayerCreatorProvider, LayerCreator)], when: String): Unit = {
    val context = new LayerCreatorContext(cpg)
    layers.foreach { case (provider, layer) =>
      val applied = Overlays.appliedOverlays(cpg)
      val missing = layer.dependsOn.filterNot(applied.contains)
      if (missing.nonEmpty) {
        throw new RuntimeException(
          s"--layer '${provider.name}': it depends on ${missing.mkString(", ")}, which the graph does not have " +
            s"(it has ${applied.mkString(", ")}). Also name the layers it depends on with --layer, or leave out " +
            s"--layer '${provider.name}' to build without it."
        )
      }
      if (applied.contains(layer.overlayName)) {
        throw new RuntimeException(
          s"--layer '${provider.name}': its overlay ${layer.overlayName} is already in the graph. Leave out " +
            s"--layer '${provider.name}', or build from a graph without it."
        )
      }
      println(s"[+] Applying layer ${provider.name} $when the default overlays")
      try {
        layer.run(context)
      } catch {
        case NonFatal(exception) =>
          throw new RuntimeException(
            s"--layer '${provider.name}': the layer failed (see the cause below). Fix or update the plug-in jar " +
              s"that provides it, or leave out --layer '${provider.name}' to build without it.",
            exception
          )
      }
    }
  }

  case class ParserConfig(
    inputPath: String = "",
    outputCpgFile: String = DefaultCpgOutFile,
    namespaces: Seq[String] = Seq.empty,
    enhance: Boolean = true,
    enhanceOnly: Boolean = false,
    language: String = "",
    listLanguages: Boolean = false,
    maxNumDef: Int = DefaultOverlays.defaultMaxNumberOfDefinitions,
    dataFlowPlugins: Seq[String] = Seq.empty,
    layers: Seq[String] = Seq.empty
  )

  private def parseConfig(parserArgs: Seq[String]): Try[ParserConfig] = {
    Try {
      optionParser
        .parse(parserArgs, ParserConfig())
        .getOrElse(
          throw new RuntimeException(s"Error while not parsing command line options: `${parserArgs.mkString(",")}`")
        )
    }
  }

}
