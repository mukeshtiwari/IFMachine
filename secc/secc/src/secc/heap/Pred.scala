package secc.heap

import secc.pure._

case class Pred(name: String, in: List[Sort], out: List[Sort]) extends Parametric[Pred] {
  override def toString = name

  def params = Set(in.flatMap(_.free) ++ out.flatMap(_.free): _*)
  def rename(re: TRen) = Pred(name, in map (_ rename re), out map (_ rename re))
  def subst(ty: Typing) = Pred(name, in map (_ subst ty), out map (_ subst ty))

  def apply(in: Pure*)(out: Pure*) = Chunk(this, in.toList, out.toList)
}