package io.joern.joerncli

import io.joern.dataflowengineoss.plugin.DataFlowPlugin
import io.shiftleft.semanticcpg.layers.{LayerCreator, LayerCreatorProvider}

import java.util.ServiceLoader
import scala.jdk.CollectionConverters.*

/** The data-flow plug-ins and layers that plug-in jars on joern-parse's class path provide, found through
  * `java.util.ServiceLoader` and selected by `--data-flow-plugin <name>` and `--layer <name>`.
  */
private[joerncli] object PluginProviders {

  private def defaultClassLoader: ClassLoader = Thread.currentThread().getContextClassLoader

  /** The data-flow plug-ins on the class path of `classLoader`, sorted by name. */
  def dataFlowPluginsAvailable(classLoader: ClassLoader = defaultClassLoader): Seq[DataFlowPlugin] =
    ServiceLoader.load(classOf[DataFlowPlugin], classLoader).iterator().asScala.toSeq.sortBy(_.name)

  /** The data-flow plug-ins named by `names`, in that order. Fails on a name no plug-in has, or that two have. */
  def dataFlowPlugins(names: Seq[String], classLoader: ClassLoader = defaultClassLoader): Seq[DataFlowPlugin] =
    if (names.isEmpty) Seq.empty
    else byName(names, dataFlowPluginsAvailable(classLoader), "--data-flow-plugin", "data-flow plug-in")(_.name)

  /** The layer providers on the class path of `classLoader`, sorted by name. */
  def layerProviders(classLoader: ClassLoader = defaultClassLoader): Seq[LayerCreatorProvider] =
    ServiceLoader.load(classOf[LayerCreatorProvider], classLoader).iterator().asScala.toSeq.sortBy(_.name)

  /** The providers named by `names`, in that order. Fails on a name no provider has, or that two providers have, and on
    * a provider that gives no layer.
    */
  def layers(names: Seq[String], classLoader: ClassLoader = defaultClassLoader): Seq[LayerCreatorProvider] =
    if (names.isEmpty) Seq.empty
    else {
      val providers = byName(names, layerProviders(classLoader), "--layer", "layer")(_.name)
      providers.foreach { provider =>
        if (provider.first().isEmpty && provider.last().isEmpty) {
          throw new IllegalArgumentException(
            s"--layer '${provider.name}': the plug-in gives no layer to run first or last. Fix the plug-in jar that " +
              s"provides it, or leave out --layer '${provider.name}' to build without it."
          )
        }
      }
      providers
    }

  /** The layers `providers` give to run before the default overlays, each created once, in dependency order. */
  def firstLayers(providers: Seq[LayerCreatorProvider]): Seq[(LayerCreatorProvider, LayerCreator)] =
    inDependencyOrder(providers.flatMap(provider => provider.first().map(provider -> _)))

  /** The layers `providers` give to run after the default overlays, each created once, in dependency order. */
  def lastLayers(providers: Seq[LayerCreatorProvider]): Seq[(LayerCreatorProvider, LayerCreator)] =
    inDependencyOrder(providers.flatMap(provider => provider.last().map(provider -> _)))

  /** `layers` ordered so that every layer comes after the layers among them that its `dependsOn` names, and otherwise
    * in the order given. A dependency that is not among `layers` is left to the caller: it must have been applied
    * before. Fails on a cycle among `layers`.
    */
  def inDependencyOrder(
    layers: Seq[(LayerCreatorProvider, LayerCreator)]
  ): Seq[(LayerCreatorProvider, LayerCreator)] = {
    val byOverlay  = layers.map { case entry @ (_, layer) => layer.overlayName -> entry }.toMap
    val ordered    = scala.collection.mutable.ArrayBuffer.empty[(LayerCreatorProvider, LayerCreator)]
    val done       = scala.collection.mutable.Set.empty[String]
    val inProgress = scala.collection.mutable.Set.empty[String]

    def visit(entry: (LayerCreatorProvider, LayerCreator)): Unit = {
      val (provider, layer) = entry
      if (!done.contains(layer.overlayName)) {
        if (!inProgress.add(layer.overlayName)) {
          throw new IllegalArgumentException(
            s"--layer '${provider.name}': the named layers depend on each other in a cycle. Leave out one of the " +
              s"layers in the cycle, or fix the plug-in jar that provides them."
          )
        }
        layer.dependsOn.flatMap(byOverlay.get).foreach(visit)
        inProgress.remove(layer.overlayName)
        done.add(layer.overlayName)
        ordered.addOne(entry)
      }
    }

    layers.foreach(visit)
    ordered.toSeq
  }

  /** The provider each of `names` selects, with an error that says how to fix a name none or several providers have. */
  private def byName[P](names: Seq[String], providers: Seq[P], option: String, kind: String)(
    nameOf: P => String
  ): Seq[P] =
    names.map { name =>
      providers.filter(nameOf(_) == name) match {
        case Seq(provider) => provider
        case Seq()         =>
          val available = if (providers.isEmpty) "none" else providers.map(nameOf).mkString(", ")
          throw new IllegalArgumentException(
            s"$option '$name': no $kind has that name (available: $available). Give one of the available names, " +
              s"add the plug-in jar that provides '$name' to joern-cli's lib folder, or leave out $option '$name' " +
              s"to build without it."
          )
        case _ =>
          throw new IllegalArgumentException(
            s"$option '$name': more than one plug-in jar in joern-cli's lib folder provides a $kind with that name. " +
              s"Remove all but one of them."
          )
      }
    }
}
