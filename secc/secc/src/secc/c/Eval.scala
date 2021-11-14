package secc.c

import secc.pure.Pure
import secc.pure.Const
import secc.error
import secc.pure.Sort
import secc.pure.Fun
import secc.pure.Rewrite
import secc.pure.Var
import secc.pure.Ex
import secc.pure.All
import secc.pure.Simplify

object Eval {
  import Prove.prove
  import Prove.consume
  import Prove.produce
  import Verify.initializeBox

  def rvals(exprs: List[Expr], st0: State, ctx: Context): List[(List[Pure], State)] = exprs match {
    case Nil =>
      List((Nil, st0))

    case expr :: rest => // XXX: right-to-left, should be parallel
      for (
        (xs, st1) <- rvals(rest, st0, ctx);
        (x, st2) <- rval(expr, st1, ctx)
      ) yield (x :: xs, st2)
  }

  def truth(arg: Pure): Pure = arg.typ match {
    case Sort.bool => arg
    case Sort.int => arg !== 0
    case Sort.pointer(_) => arg !== Fun._null()
    case _ => throw error.InvalidProgram("not boolean", arg)
  }

  def app(fun: Fun, args: Pure*) = {
    val _args = for ((typ, arg) <- fun.args zip args) yield typ match {
      case Sort.bool => truth(arg)
      case _ => arg
    }
    fun(_args: _*)
  }

  def add(arg1: Pure, arg2: Pure, ctx: Context) = (arg1.typ, arg2.typ) match {
    case (Sort.pointer(elem), ctx.int) => ctx index (arg1, arg2)
    case (ctx.int, ctx.int) => arg1 + arg2
    case _ => throw error.InvalidProgram("invalid arithmetic operation", arg1 + " + " + arg2, arg1.typ, arg2.typ)
  }

  def sub(arg1: Pure, arg2: Pure, ctx: Context) = (arg1.typ, arg2.typ) match {
    case (Sort.pointer(elem), ctx.int) => ctx index (arg1, -arg2)
    case (ctx.int, ctx.int) => arg1 - arg2
    case _ => throw error.InvalidProgram("invalid arithmetic operation", arg1 + " - " + arg2, arg1.typ, arg2.typ)
  }

  def lower(arg1: Pure, arg2: Pure, ctx: Context) = (arg1.typ, arg2.typ) match {
    case (Sort.sec, Sort.sec) => arg1 lower arg2
    case (ctx.int, ctx.int) => arg1 <= arg2 // TODO: other numeric types
    case _ => throw error.InvalidProgram("invalid comparison operation", arg1 + " <= " + arg2, arg1.typ, arg2.typ)
  }

  def rval_low_test(expr: Expr, st0: State, ctx: Context): List[(Pure, State)] = {
    for ((_res, st1) <- rval(expr, st0, ctx)) yield {
      val _test = truth(_res)
      val relational = _test.isRelational
      if (relational && ctx.isInPureMode)
        throw error.VerificationFailure("effects", "relational conditional in pure mode in eval", _test)
      if (!relational && !ctx.isInPureMode)
        prove(_test :: st1.attacker, st1, ctx)
      (_test, st1)
    }
  }

  def asg(lhs: Expr, rhs: Expr, st0: State, ctx: Context): List[(Pure, Pure, State)] = lhs match {
    case id: Id if (st0.store contains id) =>
      ctx.checkWrite(id)
      val _old = st0.store(id)
      for (
        (_rhs, st1) <- rval(rhs, st0, ctx)
      ) yield {
        (_old, _rhs, st1 assign (id, _rhs))
      }

    case Index(base, index) =>
      val expr = PreOp("*", BinOp("+", base, index))
      asg(expr, rhs, st0, ctx)

    case PreOp("*", ptr) =>
      ctx.checkStore()
      for (
        (_rhs, st1) <- rval(rhs, st0, ctx);
        (_ptr, st2) <- rval(ptr, st1, ctx)
      ) yield {
        val (_sec, _old, st3) = st2 store (_ptr, _rhs)
        prove(_ptr :: _sec, st3, ctx)
        prove(_rhs :: _sec, st3, ctx)
        (_old, _rhs, st3)
      }

    case Arrow(ptr, field) =>
      for (
        (_rhs, st1) <- rval(rhs, st0, ctx);
        (_ptr, st2) <- rval(ptr, st1, ctx)
      ) yield {
        ctx.checkStore(_ptr.typ, field)
        val _ptr_field = ctx arrow (_ptr, field)
        val (_sec, _old, st3) = st2 store (_ptr_field, _rhs)
        prove(_ptr_field :: _sec, st3, ctx)
        prove(_rhs :: _sec, st3, ctx)
        (_old, _rhs, st3)
      }
  }

  // https://en.cppreference.com/w/cpp/language/eval_order
  def rval(expr: Expr, st0: State, ctx: Context): List[(Pure, State)] = expr match {
    case BinOp(",", fst, snd) =>
      for (
        (_fst, st1) <- rval(fst, st0, ctx);
        (_snd, st2) <- rval(fst, st1, ctx)
      ) yield (_snd, st2)

    case NULL =>
      List((Fun._null(), st0))

    case id: Id if (st0.store contains id) =>
      ctx.checkRead(id)
      List((st0 store id, st0))

    case id: Id if (ctx.consts contains id) =>
      List((ctx consts id, st0))

    case id: Id if ctx.isInPureOrGhostMode && (ctx.sig contains id.name) =>
      val _fun = ctx sig id.name
      List((_fun(), st0))

    case id: Id =>
      throw error.InvalidProgram("invalid identifier", expr, st0)

    case Lit(arg: Int) =>
      List((Const(arg.toString, Sort.int), st0))

    case PreOp("&", id: Id) =>
      throw error.InvalidProgram("cannot take address of variable", expr, st0)

    case PreOp("&", PreOp("*", ptr)) =>
      rval(ptr, st0, ctx)

    case PreOp("&", Index(base, index)) =>
      val expr = BinOp("+", base, index)
      rval(expr, st0, ctx)

    case PreOp("&", Arrow(ptr, field)) =>
      for ((_ptr, st1) <- rval(ptr, st0, ctx)) yield {
        val _ptr_field = ctx arrow (_ptr, field)
        (_ptr_field, st1)
      }

    case PreOp("*", ptr) =>
      ctx.checkLoad()
      for ((_ptr, st1) <- rval(ptr, st0, ctx)) yield {
        val (_sec, _res) = st1 load _ptr
        (_res, st1)
      }

    case Index(arg, index) =>
      val expr = PreOp("*", BinOp("+", arg, index))
      rval(expr, st0, ctx)

    case Arrow(ptr, field) =>
      for ((_ptr, st1) <- rval(ptr, st0, ctx)) yield {
        ctx.checkLoad(_ptr.typ, field)
        val _ptr_field = ctx arrow (_ptr, field)
        val (_sec, _res) = st1 load _ptr_field
        (_res, st1)
      }

    case PreOp("++", arg) =>
      for ((_, _rhs, st1) <- asg(arg, BinOp("+", arg, Lit(1)), st0, ctx))
        yield (_rhs, st1)
    case PreOp("--", arg) =>
      for ((_, _rhs, st1) <- asg(arg, BinOp("-", arg, Lit(1)), st0, ctx))
        yield (_rhs, st1)

    case PostOp("++", arg) =>
      for ((_val, _, st1) <- asg(arg, BinOp("+", arg, Lit(1)), st0, ctx))
        yield (_val, st1)
    case PostOp("--", arg) =>
      for ((_val, _, st1) <- asg(arg, BinOp("-", arg, Lit(1)), st0, ctx))
        yield (_val, st1)

    case BinOp("=", lhs, rhs) =>
      for ((_, _rhs, st1) <- asg(lhs, rhs, st0, ctx))
        yield (_rhs, st1)

    case BinOp("==", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx)) yield {
        (_arg1 === _arg2, st1)
      }

    case BinOp("!=", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 !== _arg2, st1)

    case PreOp("-", arg) =>
      for ((_arg, st1) <- rval(arg, st0, ctx))
        yield (-_arg, st1)

    case PreOp("+", arg) =>
      for ((_arg, st1) <- rval(arg, st0, ctx))
        yield (+_arg, st1)

    case PreOp("!", arg) =>
      for ((_arg, st1) <- rval(arg, st0, ctx))
        yield (!truth(_arg), st1)

    case BinOp("+", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (add(_arg1, _arg2, ctx), st1)

    case BinOp("-", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (sub(_arg1, _arg2, ctx), st1)

    case BinOp("*", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 * _arg2, st1)

    case BinOp("/", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 / _arg2, st1)

    case BinOp("%", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 % _arg2, st1)

    case BinOp("<=", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 <= _arg2, st1)

    case BinOp("<", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 < _arg2, st1)

    case BinOp(">=", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 >= _arg2, st1)

    case BinOp(">", arg1, arg2) =>
      for ((List(_arg1, _arg2), st1) <- rvals(List(arg1, arg2), st0, ctx))
        yield (_arg1 > _arg2, st1)

    // don't fork if the rhs has no side effects
    case BinOp("||", arg1, arg2) if !Syntax.hasEffects(arg2) =>
      for (
        (_arg1, st1) <- rval_low_test(arg1, st0, ctx);
        (_arg2, st2) <- rval(arg2, st1, ctx)
      ) yield (truth(_arg1) || truth(_arg2), st2)

    case BinOp("&&", arg1, arg2) if !Syntax.hasEffects(arg2) =>
      for (
        (_arg1, st1) <- rval_low_test(arg1, st0, ctx);
        (_arg2, st2) <- rval(arg2, st1, ctx)
      ) yield (truth(_arg1) && truth(_arg2), st2)

    // shortcut evaluation yields two states
    case BinOp("||", arg1, arg2) =>
      val _arg1_st = rval_low_test(arg1, st0, ctx)

      val _true = for (
        (_arg1, st1) <- _arg1_st;
        st1_true <- st1 && truth(_arg1)
      ) yield (secc.pure.True, st1_true)

      val _false = for (
        (_arg1, st1) <- _arg1_st;
        st1_false <- st1 && !truth(_arg1);
        (_arg2, st2) <- rval(arg2, st1_false, ctx)
      ) yield (_arg2, st2)

      _true ++ _false

    // shortcut evaluation yields two states
    case BinOp("&&", arg1, arg2) =>
      val _arg1_st = rval_low_test(arg1, st0, ctx)

      val _false = for (
        (_arg1, st1) <- _arg1_st;
        st1_false <- st1 && !truth(_arg1)
      ) yield (secc.pure.False, st1_false)

      val _true = for (
        (_arg1, st1) <- _arg1_st;
        st1_true <- st1 && truth(_arg1);
        (_arg2, st2) <- rval(arg2, st1_true, ctx)
      ) yield (_arg2, st2)

      _false ++ _true

    case Question(test, left, right) if !Syntax.hasEffects(left) && !Syntax.hasEffects(right) =>
      for (
        (_test, st1) <- rval_low_test(test, st0, ctx);
        (_left, st2) <- rval(left, st1, ctx);
        (_right, st3) <- rval(right, st2, ctx)
      ) yield (truth(_test) ? (_left, _right), st1)

    case Question(test, left, right) =>
      val _test_st = rval_low_test(test, st0, ctx)

      val _true = for (
        (_test, st1) <- _test_st;
        st1_true <- st1 && truth(_test);
        (_left, st2) <- rval(left, st1_true, ctx)
      ) yield (_left, st2)

      val _false = for (
        (_test, st1) <- _test_st;
        st1_false <- st1 && !truth(_test);
        (_right, st2) <- rval(right, st1_false, ctx)
      ) yield (_right, st2)

      _true ++ _false

    case FunCall(id, args) if ctx.mode == Mode.ghost && (ctx.sig contains id.name) =>
      val _fun = ctx sig id.name
      for ((_args, st1) <- rvals(args, st0, ctx)) yield {
        (app(_fun, _args: _*), st1)
      }

    case expr @ FunCall(id, args) =>
      if (!(ctx.specs contains id))
        throw error.InvalidProgram("no specification", expr)

      val specs = ctx specs id
      val Prepost(pres, posts, fails, shared, isLemma, isAtomic, isPure) = Prepost(specs)
      val pre = And(pres)
      val post = And(posts)

      for (fail <- fails) {
        throw error.VerificationFailure(fail, "failure caused by propagating fails annotation on callee", id)
      }

      ctx.checkCall(expr, isLemma, isAtomic, isPure)

      val (typ, params, _) = ctx funs id
      val xr = ctx arbitrary (Id.result, typ)
      val ids = params map { case Formal(typ, name) => Id(name) }

      if (ids.length != args.length) {
        throw error.InvalidProgram("number of arguments does not match number of parameters")
      }

      for (
        (_args, st1) <- rvals(args, st0, ctx);
        // Atomic functions and lemmas have no boxes
        () = if (isLemma || isAtomic) {} else { checkSharedCompatible(st1.box, shared, Store(ids, _args), ctx) };
        st2 <- if (isLemma || isAtomic) { List(st1) } else { instantiateRely(st1, ctx) };
        (env, st3) <- consume(pre, st2.store ++ Store(Id.result :: ids, xr :: _args), st2, ctx);
        (_, st4, _) <- produce(post, env, st3, ctx, bind = false) // Note: ctx is unchanged for bind = false
      ) yield {
        if (isAtomic) {
          (xr, st4.doAtomicCall())
        } else {
          (xr, st4)
        }
      }
  }

  def checkSharedCompatible(box0: Box, shared: Option[Shared], params1: Store, ctx0: Context): Unit = shared foreach {
    shared =>
    val st0 = State.default

    for (
      (env1, st1, ctx1) <- produce(box0.assrt, box0.params, st0, ctx0, bind = true);
      (st1_, st7) <- consume(shared.assrt, env1, st1, ctx1);
      (env2, st2, ctx2) <- produce(shared.assrt, params1, st7, ctx0, bind = true);
      (st2_, st9) <- consume(box0.assrt, env2, st2, ctx2);
      () = if (!st9.isPure) {
        throw error.VerificationFailure(
          "memory",
          "shared spec of called function is incompatible to shared spec of calling function")
      };

      (env3, st3, ctx3) <- produce(box0.assrt, box0.params, st0, ctx0, bind = true);
      (st3_, st8) <- consume(shared.assrt, env3, st3, ctx3);
      (env4, st4, ctx4) <- produce(shared.assrt, params1, st8, ctx0, bind = true);
      (st4_, _) <- consume(box0.assrt, env4, st4, ctx4)
    // no second check necessary, all possibilities are already covered by first test
    ) yield {
      val r0 = eval(box0.rely, st1.store, List(st3.store), ctx1)
      val r1 = eval(shared.rely, st1_, List(st3_), ctx2)
      val g0 = eval(box0.guarantee, st2.store, List(st4.store), ctx1)
      val g1 = eval(shared.guarantee, st2_, List(st4_), ctx2)

      prove((r0 ==> r1) && (g1 ==> g0), st0, ctx0)
    }
  }

  def instantiateRely(st0: State, ctx0: Context): List[State] = {
    // Mode.ghost required for havocBox only...
    // I think that the call to checkWrite in Context.arbitrary is at least debatable as
    // checkWrite checks for valid writes from the program perspective while arbitrary
    // is used internally?
    val st1 = st0.havocBox(ctx0 enter Mode.ghost)
    st1 && rely(st1.box, st0.store filter { case (k,v) => st1.box.inst contains k }, ctx0);
  }

  def eval_low_test(expr: Expr, env: Store, st: State, ctx: Context): Pure = {
    val _test = eval_test(expr, env, st.old, ctx)
    val relational = _test.isRelational

    if (relational && ctx.isInPureMode)
      throw error.VerificationFailure("effects", "relational conditional in pure mode in eval", _test)
    if (!relational && !ctx.isInPureMode) {
      prove(_test :: st.attacker, st, ctx)
    }
    _test
  }

  def eval_test(expr: Expr, st: Store, old: List[Store], ctx: Context) = {
    truth(eval(expr, st, old, ctx))
  }

  def axiom(expr: Expr, st: Store, ctx: Context): Pure = {
    val pure = eval(expr, st, Nil, ctx)
    if (!pure.free.isEmpty)
      throw error.InvalidProgram("invalid axiom", "free variables: " + pure.free)
    // ensure that function definitions are applied
    Simplify.simplify(pure, ctx.rewrites)
  }

  def lemma(expr: Expr, ind: Option[Id], st: State, ctx: Context): Pure = {
    val pure = axiom(expr, st.store, ctx)

    if(pure.isRelational)
        throw error.VerificationFailure("relational lemmas currently unsupported")

    def check(what: String, phi: Pure) {
        print(what + phi + " ... ")
        prove(phi, st, ctx)
        println("∎")
    }

    def guarded_int(x: Var, phi: Pure): Boolean = {
      phi match {
        case Pure.imp(left, right) =>
          val prems = Pure.and.flatten(left)
          prems exists {
            case Pure.le(Const.zero, `x`) => true
            case Pure.ge(`x`, Const.zero) => true
            case _ => false
          }
        case _ =>
          println("not an implication " + phi)
          false
      }
    }


    def low_var(x: Var, phi: Pure): Boolean = {
      phi match {
        case Pure.imp(left, right) =>
          val prems = Pure.and.flatten(left)
          prems exists {
            case Pure.haslabel(`x`, secc.pure.Low) => true
            case _ => false
          }
        case _ =>
          false
      }
    }

    ind match {
      case None =>
        check("proving: ", pure)

      case Some(Id(name)) =>
        val All(params, body) = pure

        val (x, typ) = params find (_.name == name) match {
          case Some(x@Var(`name`, typ, None)) =>
            (x, typ)
          case _ =>
            throw error.InvalidProgram("invalid identifier for induction", name)
        }

        // if(body.isRelational && !low_var(x, body))
        //   throw error.VerificationFailure("induction for relational property needs premise " + name + " :: low")

        typ match {
          case Sort.int =>
            // check if body has a lower bound
            if(!guarded_int(x, body))
              throw error.VerificationFailure("induction over int needs premise 0 <= " + name)

            val y = Var.fresh(name, typ)

            val su0 = Map(x -> Const.zero)
            val base = All(params, body subst su0)

            val su1 = Map(x -> y)
            val su2 = Map(x -> (y + 1: Pure))
            val hyp = All(params, body subst su1)
            val goal = body subst su2
            val step = All(params ++ Set(y), hyp ==> goal)

            check("base: ", base)
            check("step: ", step)

          case Sort.list(elem) =>
            val a = Var.fresh("a", elem)
            val y = Var.fresh(name, typ)

            val su0 = Map(x -> Const.nil)
            val base = All(params, body subst su0)

            val su1 = Map(x -> y)
            val su2 = Map(x -> Pure.cons(a, y))
            val hyp = All(params, body subst su1)
            val goal = body subst su2
            val step = All(params ++ Set(a, y), hyp ==> goal)

            check("base: ", base)
            check("step: ", step)

          case _ =>
            throw error.InvalidProgram("unsupported type for induction", name, typ)
        }
    }
    pure
  }

  def rewrite(expr: Expr, st: Store, ctx: Context): Rewrite = eval(expr, st, Nil, ctx) match {
    case pure if !pure.free.isEmpty =>
      throw error.InvalidProgram("invalid rewrite", "free variables: " + pure.free)
    case Pure._eq(lhs, rhs) =>
      Rewrite(lhs, rhs)
    case Pure.imp(pre, Pure._eq(lhs, rhs)) =>
      Rewrite(lhs, rhs, Some(pre))
    case All(bound, Pure._eq(lhs, rhs)) =>
      Rewrite(lhs, rhs)
    case All(bound, Pure.imp(pre, Pure._eq(lhs, rhs))) =>
      Rewrite(lhs, rhs, Some(pre))

    case Pure.eqv(lhs, rhs) =>
      Rewrite(lhs, rhs)
    case Pure.imp(pre, Pure.eqv(lhs, rhs)) =>
      Rewrite(lhs, rhs, Some(pre))
    case All(bound, Pure.eqv(lhs, rhs)) =>
      Rewrite(lhs, rhs)
    case All(bound, Pure.imp(pre, Pure.eqv(lhs, rhs))) =>
      Rewrite(lhs, rhs, Some(pre))

    case _ =>
      throw error.InvalidProgram("invalid rewrite", "not one of", "lhs == rhs", "pre ==> lhs == rhs")
  }

  def rely(box: Box, inst0: Store, ctx: Context): Pure = {
    eval(box.rely, box.inst, List(inst0), ctx)
  }

  def guarantee(box: Box, inst1: Store, ctx: Context): Pure = {
    eval(box.guarantee, inst1, List(box.inst), ctx)
  }

  def eval(assrt: Assert, st: Store, old: List[Store], ctx: Context): Pure = assrt match {
    case expr: Expr =>
      eval(expr, st, old, ctx)
    case And(left, right) =>
      val _left = eval(left, st, old, ctx)
      val _right = eval(right, st, old, ctx)
      _left && _right
    case Cond(test, left, right) =>
      val _test = eval(test, st, old, ctx)
      val _left = eval(left, st, old, ctx)
      val _right = eval(right, st, old, ctx)
      _test ? (_left, _right)
    case Exists(params, body) =>
      val env = params map ctx.arbitrary
      val st_ = st ++ env
      val bound = env.map(_._2)
      val _body = eval(body, st_, old, ctx)
      Ex(bound, _body)
    case _ =>
      throw error.InvalidProgram("cannot evaluate in pure context: ", assrt)
  }

  def eval(expr: Expr, st: Store, old: List[Store], ctx: Context): Pure = expr match {
    case NULL => /* not so nice, we have null */
      Fun._null()

    case id: Id if st contains id =>
      st(id)

    case id: Id if ctx.consts contains id =>
      ctx consts id

    case id: Id if ctx.sig contains id.name =>
      val _fun = ctx sig id.name
      _fun()

    case id: Id =>
      throw error.InvalidProgram("invalid identifier", expr, st)

    case Lit(arg: Int) =>
      Const(arg.toString, Sort.int)

    case PreOp("&", PreOp("*", ptr)) =>
      eval(ptr, st, old, ctx)

    case Dot(base, field) =>
      val _base = eval(base, st, old, ctx)
      ctx dot (_base, field)

    case PreOp("&", Index(base, index)) =>
      val expr = BinOp("+", base, index)
      eval(expr, st, old, ctx)

    case PreOp("&", Arrow(ptr, field)) =>
      val _ptr = eval(ptr, st, old, ctx)
      ctx arrow (_ptr, field)

    case PreOp("-", arg) =>
      val _arg = eval(arg, st, old, ctx)
      -_arg

    case PreOp("+", arg) =>
      val _arg = eval(arg, st, old, ctx)
      +_arg

    case PreOp(op, arg) if (ctx.sig contains op) =>
      val _fun = ctx sig op
      val _arg = eval(arg, st, old, ctx)
      app(_fun, _arg)

    // polymorphic operators are treated explicitly
    case BinOp("==", arg1, arg2) =>
      val _arg1 = eval(arg1, st, old, ctx)
      val _arg2 = eval(arg2, st, old, ctx)
      _arg1 === _arg2

    case BinOp("!=", arg1, arg2) =>
      val _arg1 = eval(arg1, st, old, ctx)
      val _arg2 = eval(arg2, st, old, ctx)
      _arg1 !== _arg2

    case BinOp("::", arg1, arg2) =>
      val _arg1 = eval(arg1, st, old, ctx)
      val _arg2 = eval(arg2, st, old, ctx)
      _arg1 :: _arg2

    // addition/substraction are overloaded for integers/pointer arithmetic
    case BinOp("+", arg1, arg2) =>
      val _arg1 = eval(arg1, st, old, ctx)
      val _arg2 = eval(arg2, st, old, ctx)
      add(_arg1, _arg2, ctx)

    case BinOp("-", arg1, arg2) =>
      val _arg1 = eval(arg1, st, old, ctx)
      val _arg2 = eval(arg2, st, old, ctx)
      sub(_arg1, _arg2, ctx)

    case BinOp("<=", arg1, arg2) =>
      val _arg1 = eval(arg1, st, old, ctx)
      val _arg2 = eval(arg2, st, old, ctx)
      lower(_arg1, _arg2, ctx)

    case BinOp(op, arg1, arg2) if ctx.sig contains op =>
      val _fun = ctx sig op
      val _arg1 = eval(arg1, st, old, ctx)
      val _arg2 = eval(arg2, st, old, ctx)
      app(_fun, _arg1, _arg2)

    case BinOp(op, arg1, arg2) =>
      throw error.InvalidProgram("undefined operator", op, ctx.sig)

    case Index(base, index) =>
      val _base = eval(base, st, old, ctx)
      val _index = eval(index, st, old, ctx)
      _base select _index

    case Update(base, index, arg) =>
      val _base = eval(base, st, old, ctx)
      val _index = eval(index, st, old, ctx)
      val _arg = eval(arg, st, old, ctx)
      _base store (_index, _arg)

    case FunCall(id, args) if ctx.sig contains id.name =>
      val _fun = ctx sig id.name
      val _args = args map (eval(_, st, old, ctx))
      app(_fun, _args: _*)

    case FunCall(id, args) =>
      throw error.InvalidProgram("undefined function", id, ctx.sig)

    case Question(test, left, right) =>
      val _test = eval_test(test, st, old, ctx)
      val _left = eval(left, st, old, ctx)
      val _right = eval(right, st, old, ctx)
      _test ? (_left, _right)

    case Old(inner) =>
      if (old.isEmpty)
        throw error.InvalidProgram("no old state", expr)
      val _st :: _old = old
      eval(inner, _st, _old, ctx)

    case Bind(how, params, body) =>
      val binding = params map {
        case Formal(typ, name) =>
          val id = Id(name)
          val sort = ctx resolve typ
          val x = Var(name, sort)
          (id -> x, x)
      }

      val (env, bound) = binding.unzip
      val _st = st ++ env

      how match {
        case "exists" => Ex(bound.toSet, eval(body, _st, old, ctx))
        case "forall" => All(bound.toSet, eval(body, _st, old, ctx))
      }

    case _ =>
      throw error.InvalidProgram("unexpected expression", expr)
  }

  def open(pred: String, in: List[Expr], out: List[Expr], st: State, ctx: Context) = {
    val _pred = ctx preds pred
    val (xin, xout, body) = ctx defs pred
    val _in = in map (eval(_, st.store, st.old, ctx))
    val _out = out map (eval(_, st.store, st.old, ctx))
    val env = Store(xin ++ xout, _in ++ _out)
    (_pred, _in, _out, body, env)
  }
}
