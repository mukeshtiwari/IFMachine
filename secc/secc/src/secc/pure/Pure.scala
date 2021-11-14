package secc.pure

sealed trait Pure extends Pure.term with Sugar.expr {
  def typ: Sort
  def isRelational: Boolean
}

object Pure extends Alpha[Pure, Var] {
  import Sugar._

  def and(xs: Iterable[Pure]): Pure = {
    if (xs.isEmpty) True
    else xs reduce (_ && _)
  }

  def or(xs: Iterable[Pure]): Pure = {
    if (xs.isEmpty) False
    else xs reduce (_ || _)
  }

  def eqs(xs: Iterable[(Pure, Pure)]): Pure = {
    val zs = for ((x, y) <- xs)
      yield x === y
    and(zs)
  }

  def eqs(xs: Iterable[Pure], ys: Iterable[Pure]): Pure = {
    assert(xs.size == ys.size, "length mismatch " + xs.mkString(", ") + " == " + ys.mkString(", "))
    val zs = for ((x, y) <- (xs zip ys))
      yield x === y
    and(zs)
  }

  object ite extends ternary(Fun.ite)

  object haslabel extends binary(Fun.haslabel)
  object lower extends binary(Fun.lower)

  object exp extends binary(Fun.exp)
  object times extends binary(Fun.times)
  object divBy extends binary(Fun.divBy)
  object mod extends binary(Fun.mod)

  object uminus extends unary(Fun.uminus)
  object plus extends binary(Fun.plus)
  object minus extends binary(Fun.minus)

  object _eq extends binary(Fun._eq)
  object lt extends binary(Fun.lt)
  object le extends binary(Fun.le)
  object gt extends binary(Fun.gt)
  object ge extends binary(Fun.ge)

  object not extends unary(Fun.not)
  object and extends binary(Fun.and)
  object or extends binary(Fun.or)
  object imp extends binary(Fun.imp)
  object eqv extends binary(Fun.eqv)

  object cons extends binary(Fun.cons)
  object in extends binary(Fun.in)
  object head extends unary(Fun.head)
  object tail extends unary(Fun.tail)
  object last extends unary(Fun.last)
  object init extends unary(Fun.init)

  object select extends binary(Fun.select)
  object store extends ternary(Fun.store)
}

object Const {
  def apply(name: String, typ: Sort) = {
    App(Fun(name, Nil, typ), Nil)
  }

  def unapply(expr: Pure) = expr match {
    case App(Fun(name, Nil, typ, _), Nil) =>
      Some((name, typ))
    case _ =>
      None
  }

  def int(n: Int) = Const(n.toString, Sort.int)
  def bool(b: Boolean) = Const(b.toString, Sort.bool)

  val zero = int(0)
  val nil = Fun.nil()

  /* def nil(inst: Sort.list) = new App(Fun.nil, Nil) {
    assert(fun.args.isEmpty)
    override val env = Sort.unify(fun.ret, inst, Set.empty[Param], Typing.empty)
  } */
}

case class Var(name: String, typ: Sort, index: Option[Int] = None) extends Pure with Pure.x {
  def prime = Var(name + "'", typ, index)
  def fresh(index: Int) = Var(name, typ, Some(index))
  def isRelational = false
  override def toString = name __ index
}

object Var {
  def fresh(name: String, typ: Sort): Var = {
    Var(name, typ, Some(Pure.nextIndex))
  }
}

case class App(fun: Fun, args: List[Pure]) extends Pure {
  val inst = fun.generic

  try {
    // println("type check: " + this)
    // println("instance: " + inst.toStringTyped)
    Sort.unify(inst.args, args map (_.typ))
  } catch {
    case c: Throwable =>
      println(inst.toStringTyped)
      assert(false, "ill-typed: " + this + ", cause: " + c); ???
  }

  def typ = inst.ret.instance // Note: only stable after typechecking!
  def isRelational = fun == Fun.haslabel || args.exists(_.isRelational)
  def free = Set(args flatMap (_.free): _*)
  def rename(re: Ren) = App(fun, args map (_ rename re))
  def subst(su: Subst) = App(fun, args map (_ subst su))

  override def toString = fun.format(args, 0, Non)
}

sealed trait Quant {
  def close(body: Pure, trigger: Set[Pure] = Set()): Pure = {
    val xs = body.free
    if (xs.isEmpty) body
    else Bind(this, xs, body)
  }

  def apply(bound: Iterable[Var], body: Pure): Pure = {
    apply(bound.toSet, body)
  }

  def apply(bound: Set[Var], body: Pure): Pure = {
    val xs = bound & body.free
    if (xs.isEmpty) body
    else body match {
      case Bind(q, ys, body) if q == this =>
        Bind(this, xs ++ ys, body)
      case _ =>
        Bind(this, xs, body)
    }
  }

  def unapply(bind: Bind) = bind match {
    case Bind(q, bound, body) if q == this =>
      Some((bound, body))
    case _ => None
  }
}

case object All extends Quant {
  override def toString = "forall"
}

case object Ex extends Quant {
  override def toString = "exists"
}

case class Bind(quant: Quant, bound: Set[Var], body: Pure) extends Pure with Pure.bind {
  assert(!bound.isEmpty)
  assert(body.typ == Sort.bool)

  def typ = Sort.bool
  def isRelational = body.isRelational
  def free = body.free -- bound

  def skolem = {
    val a = Pure.fresh(bound)
    body rename a
  }

  def rename(a: Ren, re: Ren) = {
    Bind(quant, bound map (_ rename a), body rename re)
  }

  def subst(a: Ren, su: Subst) = {
    Bind(quant, bound map (_ rename a), body subst su)
  }

  override def toString = {
    "(" + quant + bound.mkString(" ", ", ", ". ") + body + ")"
  }
}