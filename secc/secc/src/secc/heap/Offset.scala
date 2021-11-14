package secc.heap

import secc.error
import secc.pure.Fun
import secc.pure.Infix
import secc.pure.Left
import secc.pure.Pure
import secc.pure.Sort
import secc.pure.App

object Offset {
  def arrow(ptr: Pure, field: String, res: Sort): Fun = ptr.typ match {
    case typ @ Sort.pointer(Sort.base(struct)) =>
      Fun("@" + struct + "." + field, List(typ), Sort.pointer(res))
    case _ =>
      throw error.InvalidProgram("invalid field access", ptr, field, res)
  }

  def dot(base: Pure, field: String, res: Sort): Fun = base.typ match {
    case typ @ Sort.base(struct) =>
      Fun("!" + struct + "." + field, List(typ), res)
    case _ =>
      throw error.InvalidProgram("invalid field access", base, field, res)
  }

  def index(ptr: Pure): Fun = ptr.typ match {
    case typ @ Sort.pointer(elem) =>
      // Fun("@" + elem, List(typ, Sort.int), typ)
      Fun("+", List(typ, Sort.int), typ, Infix(Left, 7))
    case _ =>
      throw error.InvalidProgram("invalid pointer index", ptr)
  }

  def unapply(pure: Pure) = pure match {
    case App(Fun("+", List(typ @ Sort.pointer(elem), Sort.int), res, _), List(arg1, arg2)) =>
      assert(typ == res)
      Some((arg1, arg2))
    case _ =>
      None
  }
}