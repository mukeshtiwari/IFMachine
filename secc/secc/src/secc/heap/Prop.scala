package secc.heap

import secc.pure.High
import secc.pure.Pure
import secc.pure.Ren
import secc.pure.Subst
import secc.pure.Var
import secc.pure.Sort

sealed trait Prop {
  def free: Set[Var]
  def rename(re: Ren): Prop
  def subst(su: Subst): Prop
}

case class PointsTo(ptr: Pure, sec: Pure, arg: Pure) extends Prop {
  def free = ptr.free ++ sec.free ++ arg.free

  def rename(re: Ren) = PointsTo(ptr rename re, sec rename re, arg rename re)
  def subst(su: Subst) = PointsTo(ptr subst su, sec subst su, arg subst su)

  override def toString = sec match {
    case High => ptr + " |-> " + arg
    case _ => ptr + " |->[" + sec + "] " + arg
  }
}

case class Chunk(pred: Pred, in: List[Pure], out: List[Pure]) extends Prop {
  val inst = pred.generic

  try {
    // println("type check: " + this)
    // println("instance: " + inst.toStringTyped)
    // assert((in map (_.typ)) == pred.in, "ill-typed: " + this)
    // assert((out map (_.typ)) == pred.out, "ill-typed: " + this)
    Sort.unify(inst.in, in map (_.typ))
    Sort.unify(inst.out, out map (_.typ))
  } catch {
    case c: Throwable =>
      assert(false, "ill-typed: " + this + ", cause: " + c); ???
  }

  def free = Set((in flatMap (_.free)) ++ (out flatMap (_.free)): _*)
  def ptrs = Set()

  def rename(re: Ren) = Chunk(pred, in map (_ rename re), out map (_ rename re))
  def subst(su: Subst) = Chunk(pred, in map (_ subst su), out map (_ subst su))

  override def toString = {
    if (out.isEmpty) pred + "(" + in.mkString(", ") + ")"
    else pred + "(" + in.mkString(", ") + "; " + out.mkString(", ") + ")"
  }
}