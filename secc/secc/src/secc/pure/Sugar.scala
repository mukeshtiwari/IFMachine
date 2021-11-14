package secc.pure

object Sugar {
  class unary(val fun: Fun) {
    def unapply(pure: Pure) = pure match {
      case App(`fun`, List(arg)) => Some(arg)
      case _ => None
    }

    def apply(arg: Pure) = {
      App(fun, List(arg))
    }
  }

  class binary(val fun: Fun) {
    def unapply(pure: Pure) = pure match {
      case App(`fun`, List(arg1, arg2)) => Some((arg1, arg2))
      case _ => None
    }

    def apply(arg1: Pure, arg2: Pure) = {
      App(fun, List(arg1, arg2))
    }

    def flatten(expr: Pure): List[Pure] = expr match {
      case App(`fun`, List(arg1, arg2)) =>
        flatten(arg1) ++ flatten(arg2)
      case _ =>
        List(expr)
    }
  }

  class ternary(val fun: Fun) {
    def unapply(pure: Pure) = pure match {
      case App(`fun`, List(arg1, arg2, arg3)) => Some((arg1, arg2, arg3))
      case _ => None
    }

    def apply(arg1: Pure, arg2: Pure, arg3: Pure): Pure = {
      App(fun, List(arg1, arg2, arg3))
    }
  }

  trait expr {
    this: Pure =>
    def ?(left: Pure, right: Pure) = this match {
      case True => left
      case False => right
      case _ => Pure.ite(this, left, right)
    }

    def ^(that: Pure) = Pure.exp(this, that)
    def *(that: Pure) = Pure.times(this, that)
    def /(that: Pure) = Pure.divBy(this, that)
    def %(that: Pure) = Pure.mod(this, that)

    def unary_+ = { assert(this.typ == Sort.int); this }
    def unary_- = Pure.uminus(this)
    def +(that: Pure) = Pure.plus(this, that)
    def -(that: Pure) = Pure.minus(this, that)

    def ===(that: Pure) = if (this == that) {
      True
    } else if (this.typ == Sort.bool && that.typ == Sort.bool) {
      this <=> that
    } else {
      Pure._eq(this, that)
    }

    def !==(that: Pure) = !(this === that)

    def <=(that: Pure) = Pure.le(this, that)
    def <(that: Pure) = Pure.lt(this, that)
    def >=(that: Pure) = Pure.ge(this, that)
    def >(that: Pure) = Pure.gt(this, that)

    def unary_! = this match {
      case True => False
      case False => True
      case Pure.not(phi) => phi
      case _ => Pure.not(this)
    }

    def &&(that: Pure) = (this, that) match {
      case (True, _) => that
      case (False, _) => False
      case (_, True) => this
      case (_, False) => False
      case _ => Pure.and(this, that)
    }

    def ||(that: Pure) = (this, that) match {
      case (True, _) => True
      case (False, _) => that
      case (_, True) => True
      case (_, False) => this
      case _ => Pure.or(this, that)
    }

    def ==>(that: Pure): Pure = (this, that) match {
      case (True, _) => that
      case (False, _) => True
      case (_, True) => True
      case (_, False) => !this
      case _ => Pure.imp(this, that)
    }

    def <=>(that: Pure) = (this, that) match {
      case (True, _) => that
      case (False, _) => !that
      case (_, True) => this
      case (_, False) => !this
      case _ => Pure.eqv(this, that)
    }

    def isNil = this === Const.nil

    def ::(that: Pure) = Pure.haslabel(that, this)
    def lower(that: Pure) = Pure.lower(this, that)

    def in(that: Pure) = Pure.in(this, that)
    def head = Pure.head(this)
    def tail = Pure.tail(this)
    def last = Pure.last(this)
    def init = Pure.init(this)

    def select(index: Pure) = Pure.select(this, index)
    def store(index: Pure, arg: Pure) = Pure.store(this, index, arg)
  }
}