package io.joern.x2cpg.plugin

import io.joern.x2cpg.X2CpgConfig
import io.shiftleft.codepropertygraph.generated.{Cpg, DiffGraphBuilder}
import io.shiftleft.passes.CpgPass
import org.slf4j.LoggerFactory
import scopt.OParser

import java.util.ServiceLoader
import scala.jdk.CollectionConverters.*
import scala.util.control.NonFatal

/** Code that a plug-in jar provides and a frontend runs while it builds the graph: the part every frontend's plug-ins
  * share.
  *
  * A frontend that offers plug-ins defines its own subtype with the calls it makes while it builds the graph (c2cpg's
  * is `io.joern.c2cpg.plugin.C2CpgPlugin`), loads them with [[FrontendPlugins.load]], and runs
  * [[FrontendPlugins.GraphPass]] after its own passes. A plug-in jar goes on the frontend's class path (its lib folder)
  * and lists its classes in `META-INF/services`; `java.util.ServiceLoader` finds them there, and a plug-in runs only
  * when the run names it with `--plugin <name>` (see [[FrontendPlugins.commandLineOptions]]) or passes it in code. It
  * is configured once with its settings (`--plugin-arg <name>.<key>=<value>`), and [[onGraph]] is called once, after
  * the frontend's own passes and before any overlay. Each graph call writes into a diff graph of its own, applied only
  * if the call returns normally, so a failing plug-in loses its own writes and never the frontend's graph.
  */
trait FrontendPlugin {

  /** A stable name: letters, digits, `-` and `_` only. */
  def name: String

  /** The plug-in's version. */
  def version: String

  /** The plug-in configured with `settings`; called once per run, before any file is parsed. */
  def configure(settings: Map[String, String]): FrontendPlugin = this

  /** The settings the plug-in runs with. */
  def settings: Map[String, String] = Map.empty

  /** Called once, after the frontend's own passes and before any overlay, with the whole graph. */
  def onGraph(cpg: Cpg, diffGraph: DiffGraphBuilder): Unit = ()
}

object FrontendPlugins {

  private val logger = LoggerFactory.getLogger(getClass)

  private val ValidName = "[A-Za-z0-9_-]+".r

  /** The plug-ins of a run, configured and sorted by name: `inCode` and the `kind` plug-ins on the class path of
    * `classLoader` (the frontend's own, by default) that `config.pluginNames` names. The class path is searched only
    * when a name is given. Fails on a name no plug-in or several plug-ins have, so a run never goes on without the
    * plug-ins it was asked for, on an invalid or duplicate name, and on a `configure` that returns another kind.
    */
  def load[P <: FrontendPlugin](
    kind: Class[P],
    inCode: Seq[P],
    config: X2CpgConfig[?],
    classLoader: ClassLoader = getClass.getClassLoader
  ): Seq[P] = {
    val named   = if (config.pluginNames.isEmpty) Seq.empty else byName(kind, config.pluginNames, classLoader)
    val plugins = (inCode ++ named).sortBy(_.name)
    plugins.foreach { plugin =>
      check(
        ValidName.matches(plugin.name),
        s"Plug-in '${plugin.name}': a name has only letters, digits, - and _. Fix the code that provides it."
      )
    }
    val names = plugins.map(_.name)
    names.diff(names.distinct).distinct.foreach { name =>
      throw new IllegalArgumentException(s"More than one plug-in is named '$name'. Leave out all but one of them.")
    }
    plugins.map { plugin =>
      val configured = plugin.configure(config.pluginSettings.getOrElse(plugin.name, Map.empty))
      check(
        kind.isInstance(configured),
        s"--plugin '${plugin.name}': its configure returned something that is not a ${kind.getSimpleName}. Fix the " +
          s"plug-in jar that provides it, or leave out --plugin '${plugin.name}' to build without it."
      )
      kind.cast(configured)
    }
  }

  /** The `kind` plug-in each of `names` selects on the class path of `classLoader`, with an error that says how to fix
    * a name no plug-in or several plug-ins have.
    */
  private def byName[P <: FrontendPlugin](kind: Class[P], names: Seq[String], classLoader: ClassLoader): Seq[P] = {
    val available = ServiceLoader.load(kind, classLoader).iterator().asScala.toSeq.sortBy(_.name)
    names.distinct.map { name =>
      available.filter(_.name == name) match {
        case Seq(plugin) => plugin
        case Seq()       =>
          val availableNames = if (available.isEmpty) "none" else available.map(_.name).mkString(", ")
          throw new IllegalArgumentException(
            s"--plugin '$name': no ${kind.getSimpleName} has that name (available: $availableNames). Give one of the " +
              s"available names, add the plug-in jar that provides '$name' to the frontend's lib folder, or leave " +
              s"out --plugin '$name' to build without it."
          )
        case _ =>
          throw new IllegalArgumentException(
            s"--plugin '$name': more than one plug-in jar on the frontend's class path provides a " +
              s"${kind.getSimpleName} with that name. Remove all but one of them."
          )
      }
    }
  }

  /** Fails with `message` alone (no "requirement failed" prefix), so the user reads what to change. */
  private def check(condition: Boolean, message: => String): Unit =
    if (!condition) throw new IllegalArgumentException(message)

  /** `--plugin` and `--plugin-arg`, for the command line of a frontend that offers plug-ins. */
  def commandLineOptions[R <: X2CpgConfig[R]](kindName: String): OParser[?, R] = {
    val builder = OParser.builder[R]
    import builder.*
    OParser.sequence(
      opt[String]("plugin")
        .unbounded()
        .text(s"the name of a plug-in to run: a $kindName in a jar in the frontend's lib folder")
        .validate { name =>
          if (ValidName.matches(name)) success
          else failure(s"--plugin '$name': a name has only letters, digits, - and _")
        }
        .action((name, config) => config.withPlugin(name)),
      opt[String]("plugin-arg")
        .unbounded()
        .text("a setting for a plug-in: <plug-in name>.<key>=<value>")
        .validate { arg =>
          if (arg.matches("[A-Za-z0-9_-]+\\.[^=]+=.*")) success
          else failure(s"--plugin-arg '$arg' is not <plug-in name>.<key>=<value>")
        }
        .action { (arg, config) =>
          val (name, setting) = arg.splitAt(arg.indexOf('.'))
          val (key, value)    = setting.drop(1).splitAt(setting.drop(1).indexOf('='))
          config.withPluginSetting(name, key, value.drop(1))
        }
    )
  }

  /** What `change` returns, or `unchanged` if it throws: a plug-in's failure leaves the frontend's own input or node in
    * place, and is logged with `what` it was asked about.
    */
  def attempt[T](plugin: FrontendPlugin, what: String, unchanged: T)(change: => T): T = {
    try {
      change
    } catch {
      case NonFatal(exception) =>
        logger.warn(s"plug-in '${plugin.name}' failed on $what; the frontend's own is used", exception)
        unchanged
    }
  }

  /** Runs `call` with a diff graph of its own and adds its writes to `target`, only if it returns normally. */
  def runInOwnDiff(plugin: FrontendPlugin, what: String, target: DiffGraphBuilder)(
    call: DiffGraphBuilder => Unit
  ): Unit = {
    val builder = Cpg.newDiffGraphBuilder
    try {
      call(builder)
      target.absorb(builder)
    } catch {
      case NonFatal(exception) =>
        logger.warn(s"plug-in '${plugin.name}' failed on $what; its writes there are dropped", exception)
    }
  }

  /** Runs every plug-in's [[FrontendPlugin.onGraph]], each with a diff graph of its own. */
  class GraphPass(cpg: Cpg, plugins: Seq[FrontendPlugin]) extends CpgPass(cpg) {
    override def run(builder: DiffGraphBuilder): Unit = {
      plugins.foreach { plugin =>
        runInOwnDiff(plugin, "the graph", builder)(pluginBuilder => plugin.onGraph(cpg, pluginBuilder))
      }
    }
  }
}
