package secc.c

import secc.error
import secc.pure.Ex
import secc.pure.Pure
import secc.pure.Simplify
import secc.pure.Sort
import secc.pure.Var
import secc.pure.ProofUnknown

object Prove {
  import Eval._

  def prove(phi: Pure, st: State, ctx: Context): Unit = {
    // We are top-level, so this should never fail
    assert(
      phi.typ == Sort.bool,
      "not a formula: " + phi + ": " + phi.typ)

    val relational = phi.isRelational
    if (relational && ctx.isInPureMode)
      throw error.VerificationFailure("effects", "trying to prove relational assertion in pure mode ", phi)

    st.withSolver(relational) {
      solver =>
        val _phi = Simplify.simplify(phi, st.path, ctx.rewrites)
        if (_phi != phi) {
          log.debug("rewrite", phi + " ~> " + _phi)
        }

        solver assume ctx.axioms

        log.debug("prove", st.path.mkString(" && ") + " ==> " + _phi)
        _prove(_phi)

        def _valid(phi: Pure): Boolean = {
          try {
            solver isValid phi
          } catch {
          case unknown: ProofUnknown =>
            log.error("cannot prove: " + phi)
            throw unknown
          }
        }

        def _prove(phi: Pure): Unit = phi match {
          case Pure.and(phi, psi) =>
            _prove(phi)
            _prove(psi)

          case Pure.haslabel(arg, sec) =>
            assert(relational)
            if (!_valid(phi)) {
              throw error.VerificationFailure("insecure", phi, st)
            }

          case _ =>
            if (!_valid(phi)) {
              if (phi.isRelational) // just look at this subformula
                throw error.VerificationFailure("insecure", phi, st)
              else
                throw error.VerificationFailure("incorrect", phi, st)
            }
        }
    }
  }

  // Note: guarantees that returned context is unchanged if bind == false
  // this fact is used for funcalls
  def produce(add: Assert, st: State, ctx: Context, bind: Boolean): List[(Store, State, Context)] = trace.within(Produce(add), st) {
    val env: Store = st.store
    val inst: Store = Map()
    produce(add, env, inst, st, ctx, bind)
  }

  def produce(add: Assert, env: Store, st: State, ctx: Context, bind: Boolean): List[(Store, State, Context)] = trace.within(Produce(add), st) {
    val inst: Store = Map()
    produce(add, env, inst, st, ctx, bind)
  }

  def produce(add: Assert, env: Store, inst: Store, st: State, ctx: Context, bind: Boolean): List[(Store, State, Context)] = {
    _produce(add, env, inst, st, ctx, bind)
  }

  def produce(box: Box, st0: State, ctx0: Context, bind: Boolean): List[(Store, State, Context)] = {
    for ((env1, st1, ctx1) <- produce(box.assrt, st0.box.params, st0, ctx0, bind)) yield {
      (env1, st1 updateBox env1, ctx1)
    }
  }

  def _produce(add: Assert, env0: Store, inst: Store, st0: State, ctx0: Context, bind: Boolean): List[(Store, State, Context)] = add match {
    case expr: Expr =>
      val _expr = eval(expr, env0, st0.old, ctx0)
      val _prop = truth(_expr)
      for (st1 <- st0 && _prop) yield (env0, st1, ctx0)

    case PointsTo(ptr, sec, arg) =>
      val _ptr = eval(ptr, env0, st0.old, ctx0)
      val _sec = eval(sec, env0, st0.old, ctx0)
      val _arg = eval(arg, env0, st0.old, ctx0)
      val _prop = secc.heap.PointsTo(_ptr, _sec, _arg)
      val _more = (_ptr :: _sec) && (_arg :: _sec)
      for (
        st1 <- st0 && _prop;
        st2 <- st1 && _more
      ) yield (env0, st2, ctx0)

    case Chunk(pred, in, out) =>
      val _in = in map (eval(_, env0, st0.old, ctx0))
      val _out = out map (eval(_, env0, st0.old, ctx0))
      val _pred = ctx0 preds pred
      val _prop = secc.heap.Chunk(_pred, _in, _out)
      for (st1 <- st0 && _prop) yield (env0, st1, ctx0)

    /* case And(left: Expr, right: Expr) =>
      produce(new BinOp("&&", left, right), env0, inst, st0, ctx0, bind)

    case Cond(test, left: Expr, right: Expr) =>
      produce(new Question(test, left, right), env0, inst, st0, ctx0, bind) */

    case And(left, right) =>
      for (
        (env1, st1, ctx1) <- produce(left, env0, inst, st0, ctx0, bind);
        (env2, st2, ctx2) <- produce(right, env1, inst, st1, ctx1, bind)
      ) yield {
        (env2, st2, ctx2)
      }

    case Cond(test, left, right) =>
      val _test = eval_low_test(test, env0, st0, ctx0)

      val _left = for (
        st1 <- st0 && _test;
        res <- produce(left, env0, inst, st1, ctx0, bind)
      ) yield res

      val _right = for (
        st1 <- st0 && !_test;
        res <- produce(right, env0, inst, st1, ctx0, bind)
      ) yield res

      _left ++ _right

    case Exists(params, body) =>
      val _params = params.map {
        case Formal(typ, name) =>
          val id = Id(name)
          if (inst contains id)
            (id, inst(id))
          else
            (id, ctx0 arbitrary (id, typ))
      }

      val _types = params.map {
        case Formal(typ, name) =>
          val id = Id(name)
          (id, typ)
      }

      val _env = env0 ++ _params

      if (bind) {
        val ctx1 = ctx0 declareGhost _types
        val st1 = st0 assign _params
        produce(body, _env, inst, st1, ctx1, bind)
      } else {
        produce(body, _env, inst, st0, ctx0, bind)
      }
  }

  def consume(rem: Assert, st0: State, ctx: Context): List[(Store, State)] = {
    val env0 = st0.store
    consume(rem, env0, st0, ctx)
  }

  def consume(rem: Assert, env0: Store, st0: State, ctx: Context): List[(Store, State)] = {
    val ex0: Set[Id] = Set()
    for ((ex1, cond1, rem1, env1, st1) <- consume(rem, ex0, env0, st0, ctx)) yield {
      val cond2 = rem1 map (eval_test(_, env1, st1.old, ctx))
      val bound = ex1 map env1
      val xs = bound.asInstanceOf[Set[Var]]
      val prop = Ex(xs, Pure.and(cond1 ++ cond2))
      prove(prop, st1, ctx)
      (env1, st1)
    }
  }

  def bind(pat: Expr, arg: Pure, ex: Set[Id], env: Store, st: State, ctx: Context): (Set[Id], List[Pure], Store) = pat match {
    case id: Id if ex contains id =>
      if (env contains id) log.debug("rebinding", id, env(id), arg)
      (ex - id, Nil, env + (id -> arg))

    case _ =>
      val _pat = eval(pat, env, st.old, ctx)
      (ex, List(_pat === arg), env)
  }

  def bind(pats: List[Expr], args: List[Pure], ex0: Set[Id], env0: Store, st: State, ctx: Context): (Set[Id], List[Pure], Store) = (pats, args) match {
    case (Nil, Nil) =>
      (ex0, Nil, env0)

    case (arg :: args, pat :: pats) =>
      val (ex1, cond1, env1) = bind(arg, pat, ex0, env0, st, ctx)
      val (ex2, cond2, env2) = bind(args, pats, ex1, env1, st, ctx)
      (ex2, cond1 ++ cond2, env2)
  }

  def consume(rem: Assert, ex: Set[Id], env: Store, st: State, ctx: Context): List[(Set[Id], List[Pure], List[Expr], Store, State)] = {
    log.debug("consuming", rem, st)
    _consume(rem, ex, env, st, ctx)
  }

  def _consume(rem: Assert, ex0: Set[Id], env0: Store, st0: State, ctx: Context): List[(Set[Id], List[Pure], List[Expr], Store, State)] = rem match {
    // Note: we defer the evaluation of these formulas
    //       hoping that we can get some more bindings for ex0
    case expr: Expr =>
      List((ex0, Nil, List(expr), env0, st0))

    case PointsTo(ptr, sec, arg) =>
      val _ptr = eval(ptr, env0, st0.old, ctx)
      val (_pto, st1) = st0 access _ptr
      val pats = List(sec, arg)
      val args = List(_pto.sec, _pto.arg)
      val (ex1, cond1, env1) = bind(pats, args, ex0, env0, st1, ctx)
      List((ex1, cond1, Nil, env1, st1))

    case Chunk(pred, in, out) =>
      val _in = in map (eval(_, env0, st0.old, ctx))
      val _pred = ctx preds pred
      val (_chunk, st1) = st0 access (_pred, _in)
      val (ex1, cond1, env1) = bind(out, _chunk.out, ex0, env0, st1, ctx)
      List((ex1, cond1, Nil, env1, st1))

    /* case And(left: Expr, right: Expr) =>
      consume(new BinOp("&&", left, right), ex0, env0, st0, ctx)

    case Cond(test, left: Expr, right: Expr) =>
      consume(new Question(test, left, right), ex0, env0, st0, ctx) */

    case And(left, right) =>
      for (
        (ex1, cond1, rem1, env1, st1) <- consume(left, ex0, env0, st0, ctx);
        (ex2, cond2, rem2, env2, st2) <- consume(right, ex1, env1, st1, ctx)
      ) yield {
        (ex2, cond1 ++ cond2, rem1 ++ rem2, env2, st2)
      }

    case Cond(test, left, right) =>
      val _test = eval_low_test(test, env0, st0, ctx)

      val _left = for (
        st1 <- st0 && _test;
        res <- consume(left, ex0, env0, st1, ctx)
      ) yield res

      val _right = for (
        st1 <- st0 && !_test;
        res <- consume(right, ex0, env0, st1, ctx)
      ) yield res

      _left ++ _right

    case Exists(params, body) =>
      import secc.SetOps
      val ex1 = Set(params map { case Formal(_, name) => Id(name) }: _*)
      assert(ex0 disjoint ex1)
      val env1 = params map (ctx arbitrary _)
      consume(body, ex0 ++ ex1, env0 ++ env1, st0, ctx)
  }
}