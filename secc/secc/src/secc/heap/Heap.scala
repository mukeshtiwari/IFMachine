package secc.heap

import secc.error
import secc.pure.Pure
import secc.pure.Ren
import secc.pure.Subst

case class Heap(pto: List[PointsTo], chunks: List[Chunk]) {
  def free = Set((pto flatMap (_.free)) ++ (chunks flatMap (_.free)): _*)
  def rename(re: Ren) = Heap(pto map (_ rename re), chunks map (_ rename re))
  def subst(su: Subst) = Heap(pto map (_ subst su), chunks map (_ subst su))
  
  // def ptrs = pto map (_.ptr)

  /** Prepend prop to either pto or chunks */
  def &&(prop: Prop): Heap = prop match {
    case prop: PointsTo => Heap(prop :: pto, chunks)
    case prop: Chunk => Heap(pto, prop :: chunks)
  }
  
  def &&(that: Heap): Heap = {
    Heap(this.pto ++ that.pto, this.chunks ++ that.chunks)
  }

  /** Prepend props to this heap, but keep the order of props (no reversing) */
  def &&(props: List[Prop]): Heap = props match {
    case Nil =>
      this
    case prop :: rest =>
      this && rest && prop
  }

  def load(ptr: Pure, test: Pure => Boolean): Option[(Pure, Pure)] = {
    for (PointsTo(_, sec, arg) <- pto find (pto => pto.ptr.typ == ptr.typ && test(pto.ptr === ptr))) yield {
      (sec, arg)
    }
  }

  def store(ptr: Pure, arg: Pure, test: Pure => Boolean): Option[(Pure, Pure, Heap)] = {
    val (res, rest) = access(ptr, test)
    res match {
      case None => None
      case Some(PointsTo(_, sec, old)) =>
        val pto = PointsTo(ptr, sec, arg)
        Some((sec, old, rest && pto))
    }
  }

  def access(ptr: Pure, test: Pure => Boolean): (Option[PointsTo], Heap) = {
    val (res, rest) = Heap.access(ptr, pto, test)
    (res, Heap(rest, chunks))
  }

  def access(pred: Pred, in: List[Pure], test: Pure => Boolean): (Option[Chunk], Heap) = {
    val (res, rest) = Heap.access(pred, in, chunks, test)
    (res, Heap(pto, rest))
  }
}

object Heap {
  val empty = Heap(Nil, Nil)

  /**
   * Find and remove a points to assertion from the given heap,
   * such that its location is equal to loc according to the provided test predicate.
   *
   * If such an assertion exists, the result is that assertion and the remaining heap without it,
   * otherwise, the original heap is returned.
   */
  def access(ptr: Pure, heap: List[PointsTo], test: Pure => Boolean): (Option[PointsTo], List[PointsTo]) = heap match {
    case Nil =>
      (None, heap)
    case pto :: heap if pto.ptr.typ == ptr.typ && test(pto.ptr === ptr) =>
      // XXX: these two types might mismatch when fields are in play
      (Some(pto), heap)
    case pto :: heap =>
      val (res, rest) = access(ptr, heap, test)
      (res, pto :: rest)
  }

  def access(pred: Pred, in: List[Pure], heap: List[Chunk], test: Pure => Boolean): (Option[Chunk], List[Chunk]) = heap match {
    case Nil =>
      (None, heap)
    case chunk :: heap if chunk.pred == pred && test(Pure.eqs(chunk.in, in)) =>
      (Some(chunk), heap)
    case chunk :: heap =>
      val (res, rest) = access(pred, in, heap, test)
      (res, chunk :: rest)
  }
}