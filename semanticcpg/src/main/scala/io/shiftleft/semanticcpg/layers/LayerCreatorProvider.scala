package io.shiftleft.semanticcpg.layers

/** Provides layers under a name, so that a tool such as `joern-parse --layer <name>` can run layers it does not know at
  * compile time: one to run [[first]], before the default overlays, and one to run [[last]], after them. A provider
  * gives either or both.
  *
  * Implementations are found through `java.util.ServiceLoader`: a jar on the class path lists them in
  * `META-INF/services/io.shiftleft.semanticcpg.layers.LayerCreatorProvider`. A provider needs a public constructor
  * without parameters. Being on the class path changes nothing: its layers run only when it is named.
  */
trait LayerCreatorProvider {

  /** The name the layers are selected by. */
  def name: String

  /** A new instance of the layer to run before the default overlays, on the frontend's graph, if there is one. */
  def first(): Option[LayerCreator] = None

  /** A new instance of the layer to run after the default overlays, if there is one. */
  def last(): Option[LayerCreator] = None
}
