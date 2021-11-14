package secc.pure

case class SimplificationFailure(info: Any*) extends secc.error.Error

case class Rewrite(lhs: Pure, rhs: Pure, cond: Option[Pure] = None) {
}

object Simplify {
  var debug = false
  val default = Simplify(Nil)

  def simplify(expr: Pure, rw: List[Rewrite]): Pure = {
    val self = Simplify(rw)
    self(expr)
  }

  def simplify(expr: Pure, path: List[Pure], rw: List[Rewrite]): Pure = {
    val self = Simplify(rw)
    self(expr, path)
  }
}

case class Context(path: List[Pure], eqs: Subst) {
  def ::(phi: Pure) = {
    Context(phi :: path, eqs)
  }

  def +(xe: (Var, Pure)) = {
    val (x, e) = xe
    assert(!(e.free contains x), "recursive equation: " + (x === e))
    Context(path, eqs + xe)
  }

  def maps(x: Var) = {
    eqs contains x
  }

  def apply(x: Var) = {
    eqs(x)
  }

  def contains(expr: Pure) = {
    path contains expr
  }

  // override def toString = (path ++ eqs).mkString(" && ")
}

object Context {
  val empty = Context(List.empty, Subst.empty)
  // def from(path: List[Pure]) = Context(path, Subst.empty)
}

case class Simplify(rw: List[Rewrite]) extends (Pure => Pure) {
  def apply(phi: Pure, ctx: Context): Pure = {
    try {
      simplify(phi, ctx)
    } catch {
      case _: StackOverflowError =>
        throw SimplificationFailure("nonterminating simplifcation", phi)
    }

  }

  def apply(phi: Pure, path: List[Pure]): Pure = {
    val ctx = Context.empty
    // println(phi)
    // println(path)
    val _ctx = assume(path, ctx)
    // println(_ctx)
    // println()
    apply(phi, _ctx)
    // apply(phi, Context.from(path))
  }

  def apply(phi: Pure): Pure = {
    apply(phi, Context.empty)
  }

  def simplify(exprs: List[Pure], ctx: Context): List[Pure] = {
    exprs map (simplify(_, ctx))
  }

  def rewrite(exprs: List[Pure], ctx: Context): List[Pure] = {
    exprs map (rewrite(_, ctx))
  }

  def simplify(phi: Pure, ctx: Context): Pure = {
    val res = _simplify(phi, ctx)
    if (res == phi) phi // re-use of objects
    else res
  }

  def _simplify(phi: Pure, ctx: Context): Pure = phi match {
    case Pure.not(phi) =>
      !simplify(phi, ctx)

    case Pure.and(phi, psi) =>
      val (_phi, _psi) = binary(phi, true, psi, true, ctx)
      _phi && _psi

    case Pure.or(phi, psi) =>
      val (_phi, _psi) = binary(phi, false, psi, false, ctx)
      _phi || _psi

    case Pure.imp(phi, Pure.imp(psi, chi)) =>
      simplify((phi && psi) ==> chi, ctx)

    case Pure.imp(phi, psi) =>
      val (_phi, _psi) = binary(phi, true, psi, false, ctx)
      _phi ==> _psi

    case Pure._eq(left, right) =>
      val _left = simplify(left, ctx)
      val _right = simplify(right, ctx)
      literal(_left === _right, ctx)

    case Bind(q, xs, body) =>
      val _body = simplify(body, ctx) // XXX: assumes that ctx does not extend over free variables of body
      val __body = prune(_body, q, xs, true)
      q(xs, __body)

    case _ if phi.typ == Sort.bool =>
      literal(phi, ctx)

    case _ =>
      rewrite(phi, ctx)
  }

  def rewrite(expr: App, ctx: Context, rw: List[Rewrite]): Pure = rw match {
    case Nil =>
      expr
    case Rewrite(pat, rhs, cond) :: rest =>
      bind(pat, expr, Subst.empty) match {
        case None =>
          rewrite(expr, ctx, rest)
        case Some(env) =>
          cond match {
            case None =>
              simplify(rhs subst env, ctx)
            case Some(phi) =>
              val _phi = simplify(phi subst env, ctx)
              if (_phi == True)
                simplify(rhs subst env, ctx)
              else
                rewrite(expr, ctx, rest)
          }
      }
  }

  def rewrite(expr: Pure, ctx: Context): Pure = expr match {
    case x: Var if ctx maps x =>
      val y = ctx(x)
      rewrite(y, ctx)

    case x: Var =>
      x

    /* case App(fun, args) if (rw contains fun) =>
      val Rewrite(`fun`, xs, body) = rw(fun)
      val su = Subst(xs, args)
      rewrite(body subst su, ctx) */

    case App(fun, args) =>
      val expr = App(fun, rewrite(args, ctx))
      rewrite(expr, ctx, rw)

    case _ =>
      expr
  }

  def literal(phi: Pure, ctx: Context): Pure = {
    if (ctx contains False) True
    else if (ctx contains phi) True
    else if (ctx contains !phi) False
    else rewrite(phi, ctx)
  }

  def binary(
    phi: Pure, phi_pos: Boolean,
    psi: Pure, psi_pos: Boolean,
    ctx: Context,
    psi_done: Boolean = false,
    swap: Boolean = false): (Pure, Pure) =
    {
      val newctx = if (psi_pos) assume(psi, ctx) else assert(psi, ctx)
      val newphi = simplify(phi, newctx)
      val phi_done = phi == newphi

      if (phi_done && psi_done) {
        if (swap) (psi, phi)
        else (phi, psi)
      } else {
        binary(
          psi, psi_pos,
          newphi, phi_pos,
          ctx,
          phi_done, !swap)
      }
    }

  def assume(phi: Pure, ctx: Context): Context = phi match {
    case True =>
      ctx
    case Pure.not(psi) =>
      assert(psi, ctx)
    case Pure.and(phi, psi) =>
      assume(phi, assume(psi, ctx))
    case Pure._eq(x: Var, e) if !(e.free contains x) =>
      ctx + (x -> e)
    case Pure._eq(e, x: Var) if !(e.free contains x) =>
      assume(x === e, ctx)
    case _ =>
      phi :: ctx
  }

  def assert(phi: Pure, ctx: Context): Context = phi match {
    case False =>
      ctx
    case Pure.not(psi) =>
      assume(psi, ctx)
    case Pure.imp(phi, psi) =>
      assert(phi, assume(psi, ctx))
    case Pure.or(phi, psi) =>
      assert(phi, assert(psi, ctx))
    case _ =>
      !phi :: ctx
  }

  def assume(args: List[Pure], ctx: Context): Context = {
    args.foldRight(ctx)(assume)
  }

  def assert(args: List[Pure], ctx: Context): Context = {
    args.foldRight(ctx)(assert)
  }

  def prune(phi: Pure, q: Quant, bound: Set[Var], pos: Boolean): Pure = phi match {
    case Pure._eq(x: Var, e) if !(e.free contains x) && (bound contains x) =>
      if (pos && q == Ex || !pos && q == All) {
        True
      } else {
        phi
      }
    case Pure._eq(e, x: Var) if !(e.free contains x) =>
      prune(x === e, q, bound, pos)
    case Pure.not(psi) =>
      val _psi = prune(psi, q, bound, !pos)
      !_psi
    case Pure.imp(phi, psi) =>
      val _phi = prune(phi, q, bound, !pos)
      val _psi = prune(psi, q, bound, pos)
      _phi ==> _psi
    case Pure.or(phi, psi) =>
      val _phi = prune(phi, q, bound, !pos)
      val _psi = prune(psi, q, bound, !pos)
      _phi || _psi
    case Pure.and(phi, psi) =>
      val _phi = prune(phi, q, bound, pos)
      val _psi = prune(psi, q, bound, pos)
      _phi && _psi
    case _ =>
      phi
  }

  def bind(pats: List[Pure], args: List[Pure], env0: Subst): Option[Subst] = (pats, args) match {
    case (Nil, Nil) =>
      Some(env0)
    case (pat :: pats, arg :: args) =>
      for (
        env1 <- bind(pat, arg, env0);
        env2 <- bind(pats, args, env1)
      ) yield env2
    case _ =>
      None
  }

  def bind(pat: Pure, arg: Pure, env: Subst): Option[Subst] = (pat, arg) match {
    case (x: Var, _) if !(env contains x) =>
      Some(env + (x -> arg))
    case (x: Var, _) if (env contains x) && (env(x) == arg) =>
      Some(env + (x -> arg))
    case (x: Var, _) =>
      None
    case (App(fun1, pats), App(fun2, args)) if fun1 == fun2 =>
      bind(pats, args, env)
    case _ =>
      None
  }
}