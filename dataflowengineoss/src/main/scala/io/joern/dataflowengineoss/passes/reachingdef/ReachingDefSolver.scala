package io.joern.dataflowengineoss.passes.reachingdef

import io.shiftleft.codepropertygraph.generated.nodes.CfgNode

import scala.collection.mutable

/** The reaching-definitions solver of [[ReachingDefPass]]. For the problem of [[ReachingDefProblem.create]], it finds
  * the least fixpoint of `in(n)` = ∪ `out(p)` over `pred(n)` and `out(n)` = `gen(n)` ∪ (`in(n)` \ `kill(n)`) with a
  * work list:
  *
  *   - definitions are numbered 0 to their count minus one inside the solver, so that a set is an array of words of one
  *     fixed length, one bit per definition, and the sets live in arrays indexed by node number;
  *   - each set is updated in place: every set only grows on the way to the fixpoint, so `in(n)` takes the union of the
  *     current `out(p)` in place, and `out(n)` takes the new value's bits;
  *   - one set is shared where two sets are equal by definition: a node with a single predecessor `p` has `in(n)` =
  *     `out(p)`, and a node that neither generates nor kills has `out(n)` = `in(n)`;
  *   - a call kills through one set per variable it defines, shared by every call that defines that variable
  *     ([[ReachingDefTransferFunction.killMasks]]);
  *   - only the steps that compute something (a union at a node with several predecessors, a transfer at a node that
  *     generates or kills) are in the work list, and a step is queued again only when a set it reads grew.
  *
  * [[solve]] gives a `Solution` in the problem's numbering, one `BitSet` per distinct solved set, so sets shared while
  * solving stay shared. [[ReachingDefPass]] reads the solved sets through [[solveIn]], which keeps them in the solver's
  * numbering and translates a definition only when it is read.
  */
private[reachingdef] object ReachingDefSolver {

  /** The solution of `problem`: its `in` and `out` sets in the problem's numbering. */
  def solve(problem: DataFlowProblem[CfgNode, mutable.BitSet]): Solution[CfgNode, mutable.BitSet] = {
    val solved = solveWords(problem)
    import solved.*
    val asBitSet                                   = new java.util.IdentityHashMap[Array[Long], mutable.BitSet]()
    def bitSetOf(set: Array[Long]): mutable.BitSet = {
      val existing = asBitSet.get(set)
      if (existing != null) {
        existing
      } else {
        val created = mutable.BitSet.fromSpecific(new DefinitionWords(set, definitions, compactOf).iterator)
        asBitSet.put(set, created)
        created
      }
    }
    val in =
      nodes.indices.map(number => nodes(number) -> bitSetOf(inSet(number))).toMap.withDefaultValue(mutable.BitSet())
    val out = (transfer.gen ++ nodes.indices.map(number => nodes(number) -> bitSetOf(outSet(number))))
      .withDefaultValue(mutable.BitSet())
    Solution(in, out, problem)
  }

  /** The `in` sets of `problem`'s solution, read in place: each is a view of a solved set that translates a definition
    * when it is read, and nodes that share a set share its view.
    */
  def solveIn(problem: DataFlowProblem[CfgNode, mutable.BitSet]): Map[CfgNode, Set[Definition]] = {
    val solved = solveWords(problem)
    import solved.*
    val views                                     = new java.util.IdentityHashMap[Array[Long], DefinitionWords]()
    def viewOf(set: Array[Long]): Set[Definition] = {
      val existing = views.get(set)
      if (existing != null) existing
      else { val created = new DefinitionWords(set, definitions, compactOf); views.put(set, created); created }
    }
    nodes.indices.map(number => nodes(number) -> viewOf(inSet(number))).toMap.withDefaultValue(Set.empty)
  }

  /** A solved problem: the reachable nodes in order, their `in` and `out` sets in the solver's numbering, and the
    * numbering (`definitions(i)` is the problem's number of the solver's definition `i`; `compactOf` the reverse).
    */
  private final class Solved(
    val nodes: Array[CfgNode],
    val inSet: Array[Array[Long]],
    val outSet: Array[Array[Long]],
    val definitions: Array[Definition],
    val compactOf: Array[Int],
    val transfer: ReachingDefTransferFunction
  )

  private def solveWords(problem: DataFlowProblem[CfgNode, mutable.BitSet]): Solved = {
    val flowGraph = problem.flowGraph.asInstanceOf[ReachingDefFlowGraph]
    val transfer  = problem.transferFunction.asInstanceOf[ReachingDefTransferFunction]
    val nodes     = flowGraph.allNodesReversePostOrder.toArray
    val numberOf  = flowGraph.nodeToNumber
    val count     = flowGraph.numberToNode.size
    val reached   = nodes.length

    // The flow graph numbers its reachable nodes 0 to `reached` - 1 in this order, the others after them.
    val genSets  = Array.tabulate(count)(number => transfer.gen(flowGraph.numberToNode(number)))
    val killSets = Array.tabulate(count)(number => transfer.killMasks(flowGraph.numberToNode(number)))

    // The solver's own numbering: the definitions some node generates, in the problem's order. Every `in` and `out` set
    // holds only such definitions, so a killed node that no node generates can be dropped from `kill`.
    val definitions = {
      val all = mutable.BitSet()
      genSets.foreach(all |= _)
      all.toArray
    }
    val compactOf = Array.fill(count)(-1)
    definitions.indices.foreach(index => compactOf(definitions(index)) = index)
    val words = (definitions.length + 63) >>> 6

    def wordsOf(set: mutable.BitSet): Array[Long] = {
      val result = new Array[Long](words)
      set.foreach { definition =>
        val index = if (definition < count) compactOf(definition) else -1
        if (index >= 0) result(index >>> 6) |= 1L << (index & 63)
      }
      result
    }
    val preds: Array[Array[Int]] =
      nodes.map(node => flowGraph.pred(node).iterator.flatMap(numberOf.get).toArray.distinct)

    val inSet  = new Array[Array[Long]](count)
    val outSet = new Array[Array[Long]](count)
    val gen    = new Array[Array[Long]](reached)
    val kill   = new Array[Array[Array[Long]]](reached)
    // A variable's mask is shared by the calls that define it, so it is translated once.
    val maskWords = new java.util.IdentityHashMap[Array[Definition], Array[Long]]()
    def wordsOfMask(mask: Array[Definition]): Array[Long] = {
      val existing = maskWords.get(mask)
      if (existing != null) {
        existing
      } else {
        val created = new Array[Long](words)
        mask.foreach { definition =>
          val index = if (definition < count) compactOf(definition) else -1
          if (index >= 0) created(index >>> 6) |= 1L << (index & 63)
        }
        maskWords.put(mask, created)
        created
      }
    }
    // A node outside the reachable ones is never solved: its `out` is its `gen`.
    Range(reached, count).foreach(number => outSet(number) = wordsOf(genSets(number)))

    val unionStep    = new Array[Boolean](reached)
    val transferStep = new Array[Boolean](reached)
    Range(0, reached).foreach { number =>
      val predecessors = preds(number)
      if (predecessors.isEmpty) {
        inSet(number) = new Array[Long](words)
      } else if (predecessors.length == 1 && outSet(predecessors(0)) != null) {
        inSet(number) = outSet(predecessors(0))
      } else {
        // Several predecessors, or a single one later in the order, which has no set to share yet.
        inSet(number) = new Array[Long](words)
        unionStep(number) = true
      }
      if (genSets(number).isEmpty && killSets(number).isEmpty) {
        outSet(number) = inSet(number)
      } else {
        gen(number) = wordsOf(genSets(number))
        kill(number) = killSets(number).map(wordsOfMask)
        outSet(number) = gen(number).clone()
        transferStep(number) = true
      }
    }

    // Steps: 2 * n computes in(n) by union, 2 * n + 1 computes out(n) by transfer. A set is written by one step only.
    val owner = new java.util.IdentityHashMap[Array[Long], Integer]()
    Range(0, reached).foreach { number =>
      if (unionStep(number)) owner.put(inSet(number), 2 * number)
      if (transferStep(number)) owner.put(outSet(number), 2 * number + 1)
    }
    val readers                                   = Array.fill(2 * reached)(mutable.ArrayBuffer.empty[Int])
    def readBy(set: Array[Long], step: Int): Unit = {
      val writer = owner.get(set)
      if (writer != null && !readers(writer).contains(step)) readers(writer) += step
    }
    Range(0, reached).foreach { number =>
      if (unionStep(number)) preds(number).foreach(pred => readBy(outSet(pred), 2 * number))
      if (transferStep(number)) readBy(inSet(number), 2 * number + 1)
    }

    val queued                   = new Array[Boolean](2 * reached)
    val work                     = new java.util.ArrayDeque[Integer]()
    def enqueue(step: Int): Unit = if (!queued(step)) { queued(step) = true; work.add(step) }
    Range(0, reached).foreach { number =>
      if (unionStep(number)) enqueue(2 * number)
      if (transferStep(number)) enqueue(2 * number + 1)
    }
    while (!work.isEmpty) {
      val step   = work.poll().intValue
      val number = step >> 1
      queued(step) = false
      var grew = false
      if ((step & 1) == 0) {
        val set = inSet(number)
        preds(number).foreach { pred =>
          val from = outSet(pred)
          var i    = 0
          while (i < words) {
            val added = from(i) & ~set(i)
            if (added != 0) { set(i) |= added; grew = true }
            i += 1
          }
        }
      } else {
        val in    = inSet(number)
        val set   = outSet(number)
        val gens  = gen(number)
        val masks = kill(number)
        var i     = 0
        while (i < words) {
          var value = in(i)
          var mask  = 0
          while (mask < masks.length) { value &= ~masks(mask)(i); mask += 1 }
          val added = (value | gens(i)) & ~set(i)
          if (added != 0) { set(i) |= added; grew = true }
          i += 1
        }
      }
      if (grew) readers(step).foreach(enqueue)
    }

    new Solved(nodes, inSet, outSet, definitions, compactOf, transfer)
  }
}

/** A set of definitions held as words in a solver's numbering: bit `i` stands for definition `definitions(i)`, and
  * `compactOf` maps a definition back to its bit, or to -1. Read only; adding or removing a definition gives a new set.
  */
private[reachingdef] final class DefinitionWords(
  words: Array[Long],
  definitions: Array[Definition],
  compactOf: Array[Int]
) extends scala.collection.immutable.AbstractSet[Definition] {

  override def contains(definition: Definition): Boolean = {
    val index = if (definition >= 0 && definition < compactOf.length) compactOf(definition) else -1
    index >= 0 && (words(index >>> 6) & (1L << (index & 63))) != 0
  }

  /** The definitions in ascending order. */
  override def iterator: Iterator[Definition] = new Iterator[Definition] {
    private var word            = 0
    private var bits            = if (words.isEmpty) 0L else words(0)
    private def advance(): Unit = while (bits == 0 && word < words.length - 1) { word += 1; bits = words(word) }
    advance()
    override def hasNext: Boolean   = bits != 0
    override def next(): Definition = {
      if (bits == 0) throw new NoSuchElementException
      val bit = java.lang.Long.numberOfTrailingZeros(bits)
      bits &= bits - 1
      val definition = definitions((word << 6) + bit)
      advance()
      definition
    }
  }

  override lazy val size: Int = words.foldLeft(0)((sum, word) => sum + java.lang.Long.bitCount(word))

  override def knownSize: Int = size

  override def isEmpty: Boolean = words.forall(_ == 0)

  override def incl(definition: Definition): scala.collection.immutable.Set[Definition] =
    scala.collection.immutable.BitSet.fromSpecific(iterator) + definition

  override def excl(definition: Definition): scala.collection.immutable.Set[Definition] =
    scala.collection.immutable.BitSet.fromSpecific(iterator) - definition
}
