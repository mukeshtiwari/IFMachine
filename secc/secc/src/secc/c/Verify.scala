package secc.c

import secc.error

import secc.pure.Pure
import secc.pure.All

object Verify {
  import Eval._
  import Prove.prove
  import Prove.produce
  import Prove.consume

  var interactive: Boolean = true
  var functions: Option[List[String]] = None

  def omit(id: Id) = functions match {
    case None => false
    case Some(functions) => !(functions contains id.name)
  }

  def file(name: String, stmts: List[Global]): Unit = {
    log.shift {
      val ctx0 = specify(stmts, Context.default)
      val st0 = ctx0.defaultState
      exec(stmts, st0, ctx0)
    }
  }

  def exec(stmts: List[Global], st0: State, ctx0: Context): Unit = stmts match {
    case Nil =>
    case first :: rest =>
      for ((st1, ctx1) <- exec(first, st0, ctx0)) {
        exec(rest, st1, ctx1)
      }
  }

  def specify(stmts: List[Stmt], ctx: Context): Context = stmts match {
    case Nil =>
      ctx
    case FunDef(ret, id, params, specs, body) :: rest =>
      // if ((specs contains Lemma) && ret != Void)
      //   throw error.InvalidProgram("lemma has non void return type", ret)
      specify(
        rest,
        ctx copy (
          funs = ctx.funs + (id -> (ret, params, body)),
          specs = ctx.specs + (id -> specs)))
    case _ :: rest =>
      specify(rest, ctx)
  }

  def validateRely(rely: Expr, inst: Store, st: State, ctx: Context): Unit = {
    // Mode change only due to arbitrary...
    val ctx1 = ctx enter Mode.ghost

    val x0 = inst map (t => (t._1, ctx1 arbitrary t._1));
    val x1 = inst map (t => (t._1, ctx1 arbitrary t._1));
    val x2 = inst map (t => (t._1, ctx1 arbitrary t._1));

    val r12 = eval(rely, x1, List(x0), ctx1);
    val r23 = eval(rely, x2, List(x1), ctx1);
    val r13 = eval(rely, x2, List(x0), ctx1);
    val r22 = eval(rely, x1, List(x1), ctx1);

    prove(r22 && ((r12 && r23) ==> r13), st, ctx1)
  }

  def initializeBox(shared: Shared, st1: State, params: List[Id], ctx1: Context): List[(State, Context)] = {
    for (
      (_, st2, ctx2) <- produce(shared.assrt, st1, ctx1, bind = true);
      inst = st2.store filter (t => !(st1.store contains t._1) && t._1 != TID);
      // We have to extend the store by all all variables existentially quantified in shared.assrt
      // but not by the heap elements. Therefore produce and consume shared.assrt.
      (_, st3) <- consume(shared.assrt, st2, ctx2)
    ) yield {
      validateRely(shared.rely, inst, st1, ctx2)
      val box = Box(shared.assrt, shared.rely, shared.guarantee, inst, st1.store filter (params contains _._1))
      (st3.copy(box = box), ctx2)
    }
  }

  def verify(typ: Type, id: Id, params: List[Formal], specs: List[Spec], body: Stmt, st0: State, ctx0: Context): Unit = if(!omit(id)) {
    log.info_(id + " ... ")

    val start = System.currentTimeMillis()

    val Prepost(pres, posts, fails, shared, isLemma, isAtomic, isPure) = Prepost(specs)
    val pre = And(pres)
    val post = And(posts)

    if (isLemma && isAtomic) {
      throw error.InvalidProgram("function may be a lemma or an atomic function but not both")
    }
    if (isPure && !isLemma) {
      throw error.InvalidProgram("function must be lemma if pure")
    }
    if (shared.nonEmpty && (isLemma || isAtomic)) {
      throw error.InvalidProgram("lemmas and atomic functions must not have shared block")
    }

    val _params = (params map { case Formal(typ, name) => (Id(name), typ) })

    val ctx = if(isPure) ctx0 enter Mode.pure else if (isLemma) ctx0 enter Mode.ghost else ctx0
    val ctx1 = ctx declare _params declareGhost (Id.result, typ)

    val _ids = _params map (_._1)
    val st1 = (st0 havoc (_ids, ctx1))

    // result is the only identifier not referring to the initial state
    val old_post = Post(post, Set(Id.result))

    try {
      shared match {
        case Some(shared) =>
          for (
            (st4, ctx2) <- initializeBox(shared, st1, _ids, ctx1);
            initial = produce(pre, st4, ctx2, bind = true);
            _ = if (initial.isEmpty) {
              log.info("warning:", "precondition " + pre + " is unsatisfiable", id)
            };
            (_, st5, ctx4) <- initial
          ) {
            verify(body, post, post, st5.saveOld, ctx4)
          }

        case None =>
          val initial = produce(pre, st1, ctx1, bind = true)

          if (initial.isEmpty) {
            log.info("warning:", "precondition " + pre + " is unsatisfiable", id)
          }

          for ((_, st2, ctx2) <- initial) {
            verify(body, old_post, old_post, st2.saveOld, ctx2)
          }
      }

      val end = System.currentTimeMillis()
      val time = (end - start)

      if (fails.isEmpty) {
        log.info("success ❤ (time " + time + "ms)")
      } else {
        log.error("uncaught " + fails.mkString(" ") + " ⚡")
        throw error.VerificationFailure("uncaught " + fails.mkString(" ") + " ⚡")
      }
    } catch {
      case e @ trace.VerificationFailure(trace, msg, info @ _*) =>
        if (fails contains msg) {
          log.error("caught " + msg + " ♡")
        } else {
          log.info(msg + " ⚡")
          log.shift {
            for (more <- info) {
              log.info(more)
            }
            log.info("reverse trace (last statement first)")
            log.shift {
              for ((stmt, st) <- trace) {
                st.info()
                log.info("execute")
                log.shift {
                  log.info(stmt)
                }
              }
            }
          }
          if (!interactive)
            throw e
        }

      case e @ error.VerificationFailure(msg, info @ _*) =>
        if (fails contains msg) {
          log.info("caught " + msg + " ♡")
        } else {
          log.info(msg + " ⚡")
          for (more <- info) {
            log.info("  " + more)
          }
          if (!interactive)
            throw e
        }

      case e: error.VerificationFailure =>
        log.info("unknown verification failure ⚡")
        if (!interactive)
          throw e

      case e @ error.Error(msg, info @ _*) =>
        log.info(msg + " ⚡")
        for (more <- info) {
          log.info("  " + more)
        }
        if (!interactive)
          throw e
    }
  }

  def verify(post: Assert, st0: State, ctx0: Context) {
    for ((_, st1) <- consume(post, st0, ctx0)) {
      if (!st1.isPure) {
        val chunks = st1.heap.pto ++ st1.heap.chunks
        throw error.VerificationFailure("memory", "leaking heap chunks", chunks.mkString(" && "), "postcondition: " + post, st0)
      }
    }
  }

  def verify(first: Stmt, ret: Assert, post: Assert, st: State, ctx: Context): Unit = {
    verify(first, Nil, ret, post, st, ctx)
  }

  def verify(stmts: List[Stmt], ret: Assert, post: Assert, st: State, ctx: Context): Unit = stmts match {
    case Nil =>
      log.debug()
      log.debug("post", post)

      verify(post, st, ctx)
    case first :: rest =>
      log.debug()
      log.debug("execute", first)
      log.debug("vars   ", ctx.vars)
      log.debug("ghost  ", ctx.ghost)
      log.debug("store  ", st.store)
      log.debug("path   ", st.path)
      log.debug("pto    ", st.heap.pto)
      log.debug("chunks ", st.heap.chunks)

      trace.within(first, st) {
        verify(first, rest, ret, post, st, ctx)
      }
  }

  def exec(first: Aux, st0: State, ctx0: Context): List[(State, Context)] = first match {
    case Internal(_, f) =>
      f(st0, ctx0)

    case Prune =>
      for (st1 <- st0.stronglyConsistent)
        yield (st1, ctx0)

    case Produce(assrt) =>
      for ((_, st1, ctx1) <- produce(assrt, st0, ctx0, bind = true))
        yield (st1, ctx1)

    case Consume(assrt, msg) =>
      for (
        (env1, st1) <- consume(assrt, st0, ctx0);
        (_, st2, ctx2) <- produce(assrt, st1.store, env1, st1, ctx0, bind = true)
      ) yield {
        (st2, ctx2)
      }

    case Unfold(chunk @ Chunk(pred, in, out)) =>
      if (!(ctx0.defs contains pred))
        throw error.InvalidProgram("cannot unfold " + chunk + " (no definition)")

      val (_pred, _in, _out, body, env) = open(pred, in, out, st0, ctx0)
      val (_chunk, st1) = st0 access (_pred, _in)
      val eqs = Pure.eqs(_chunk.out, _out)
      prove(eqs, st1, ctx0)
      for ((_, st1, ctx1) <- produce(body, env, st1, ctx0, bind = false))
        yield (st1, ctx1)

    case Fold(chunk @ Chunk(pred, in, out)) =>
      if (!(ctx0.defs contains pred))
        throw error.InvalidProgram("cannot fold " + chunk + " (no definition)")

      val (_pred, _in, _out, body, env0) = open(pred, in, out, st0, ctx0)
      val _chunk = secc.heap.Chunk(_pred, _in, _out)

      for (
        (env1, st1) <- consume(body, env0, st0, ctx0);
        st2 <- st1 && _chunk
      ) yield {
        // Note: the env1 is irrelevant as all additions to st1 have been evaluated against it
        (st2, ctx0)
      }

    case Unfold(assrt) =>
      throw error.InvalidProgram("cannot unfold " + assrt + " (not a predicate)")

    case Fold(assrt) =>
      throw error.InvalidProgram("cannot unfold " + assrt + " (not a predicate)")

    case PredDef(name, in, out, body) if (ctx0.preds contains name) =>
      throw error.InvalidProgram("predicate already defined", first)

    case PredDef(name, in, out, body) =>
      val ctx1 = ctx0 predicate (name, in, out, body)
      List((st0, ctx1))

    case PureDef(name, in, out, body) if (ctx0.sig contains name) =>
      throw error.InvalidProgram("function/constant already defined", name)

    case PureDef(name, in, out, body) =>
      val ctx1 = ctx0 function (name, in, out, body)
      List((st0, ctx1))

    case Rules(exprs, true) =>
      val axioms = exprs map (axiom(_, st0.store, ctx0))
      val ctx1 = ctx0 copy (axioms = ctx0.axioms ++ axioms)
      List((st0, ctx1))

    case Rules(exprs, false) =>
      val rewrites = exprs map (rewrite(_, st0.store, ctx0))
      val ctx1 = ctx0 copy (rewrites = ctx0.rewrites ++ rewrites)
      List((st0, ctx1))

    case Lemma(expr, ind) =>
      val axioms = List(lemma(expr, ind, st0, ctx0))
      val ctx1 = ctx0 copy (axioms = ctx0.axioms ++ axioms)
      List((st0, ctx1))

    case BeginAtomicBlock =>
      for (
        (_, st1, ctx1) <- produce(st0.box, st0, ctx0 enter Mode.atomic, bind = true);
        // We cannot use st0.box because the last atomic block has modified the content
        st2 <- st1 && rely(st1.box, st0.store filter { case (k,v) => st0.box.inst contains k}, ctx1)
      ) yield {
        (st2.resetAtomicCallCounter(), ctx1)
      }

    case EndAtomicBlock =>
      for (
        (env1, st1) <- consume(st0.box.assrt, st0, ctx0)
      ) yield {
        prove(guarantee(st0.box, env1 filter { case (k,v) => st0.box.inst contains k}, ctx0), st1, ctx0)
        (st1 assign env1, ctx0.leave())
      }

    case _ =>
      throw error.InvalidProgram("unsupported ghost statement", Ghost(first))
  }

  def exec(first: Global, st0: State, ctx0: Context): List[(State, Context)] = first match {
    case first: Def =>
      List((st0, define(first, ctx0)))

    case Ghost(first) =>
      exec(first, st0, ctx0)

    case VarDef(typ, id, None, specs) =>
      val ctx1 = ctx0 declare (id, typ)
      val st1 = st0 havoc (id, ctx1)
      List((st1, ctx1))

    case VarDef(typ, id, Some(init), specs) =>
      val ctx1 = ctx0 declare (id, typ)
      val st1 = st0 havoc (id, ctx1)
      for ((_init, st2) <- rval(init, st1, ctx1)) yield {
        val st3 = st2 assign (id, _init)
        (st3, ctx1)
      }

    case FunDef(ret @ SignedInt, id @ Id.main, params @ List(), specs, Some(body)) =>
      verify(ret, id, params, specs, body, st0, ctx0)
      List((st0, ctx0))

    case FunDef(ret @ SignedInt, id @ Id.main, params @ List(Formal(SignedInt, argc), Formal(PtrType(SignedChar), argv)), specs, Some(body)) =>
      val st1 = st0 // TODO: add argv to the state
      val ctx1 = ctx0
      verify(ret, id, params, specs, body, st1, ctx1)
      List((st0, ctx0))

    case FunDef(_, Id.main, _, _, _) =>
      throw error.InvalidProgram("invalid signature for main", first)

    case FunDef(ret, id, params, specs, None) =>
      List((st0, ctx0))

    case FunDef(ret, id, params, specs, Some(body)) =>
      // verify(ret, id, params, specs, body, ctx0.defaultState, ctx0)
      verify(ret, id, params, specs, body, st0, ctx0)
      List((st0, ctx0))
  }

  def verify(first: Option[Stmt], rest: List[Stmt], ret: Assert, post: Assert, st0: State, ctx0: Context): Unit = first match {
    case None => verify(rest, ret, post, st0, ctx0)
    case Some(first) => verify(first, rest, ret, post, st0, ctx0)
  }

  def verify(first: Stmt, rest: List[Stmt], ret: Assert, post: Assert, st0: State, ctx0: Context): Unit = first match {
    case Ghost(Apply(stmt)) =>
      // stay in pure mode if we are already in that mode
      val m = if (ctx0.isInPureMode) Mode.pure else Mode.ghost
      val ctx1 = ctx0 enter m
      def f(st: State, ctx: Context) = List((st, ctx.leave))
      val reset = Ghost(Internal("restore mode " + ctx0.mode, f))
      verify(stmt, reset :: rest, ret, post, st0, ctx1)
 
    case Ghost(ApplyForall(generalize, FunCall(id, args))) =>
      if (!(ctx0.specs contains id))
        throw error.InvalidProgram("no specification", first)

      val specs = ctx0 specs id
      val Prepost(pres, posts, fails, shared, isLemma, isAtomic, isPure) = Prepost(specs)

      val ok = isLemma && isPure && shared.isEmpty && fails.isEmpty
      if(!ok)
        throw error.InvalidProgram("function not suitable for forall call ", id)

      val env = generalize map ctx0.arbitrary
      val st = st0.store ++ env
      val old = st0.old
      val bound = env.map(_._2)
      
      val _args = args map {
        arg => Eval.eval(arg, st, old, ctx0)
      }

      println(_args)

      val (typ, params, _) = ctx0 funs id
      val xr = ctx0 arbitrary (Id.result, typ)
      val ids = params map { case Formal(typ, name) => Id(name) }
      val env0 = Store(ids, _args)
      val env1 = env0 + (Id.result -> xr)

      val _pres = pres map {
        pre => Eval.eval(pre, st ++ env0, old, ctx0)
      }

      val _posts = posts map {
        post => Eval.eval(post, st ++ env1, old, ctx0)
      }

      val _pre = Pure.and(_pres)
      val _post = Pure.and(_posts)

      val phi = All(bound, _pre ==> _post)
      println(phi)
      for(st1 <- st0 && phi) {
        verify(rest, ret, post, st1, ctx0)
      }

    case first: Global =>
      for ((st1, ctx1) <- exec(first, st0, ctx0)) {
        verify(rest, ret, post, st1, ctx1)
      }

    case block @ Block(stmts) =>
      val vars = ctx0.vars
      val ghost = ctx0.ghost
      val env = st0.store filterKeys block.locals

      def cleanup(st1: State, ctx1: Context) = {
        val st2 = st1 assign env
        List((st2, ctx0))
      }

      val stmt = Ghost(Internal("leave block", cleanup))
      // TODO: not scoped properly
      verify(stmts ++ List(stmt) ++ rest, ret, post, st0, ctx0)

    case Return(None) =>
      verify(ret, st0, ctx0)

    case Return(Some(res)) =>
      for ((_res, st1) <- rval(res, st0, ctx0)) {
        val st2 = st1 assign (Id.result, _res)
        verify(ret, st2, ctx0)
      }

    case Atomic(expr) =>
      for ((_, st1) <- rval(expr, st0, ctx0))
        verify(rest, ret, post, st1, ctx0)

    case If(test, left, right) =>
      val _test_st = rval_low_test(test, st0, ctx0)

      for ((_test, st0) <- _test_st) {
        for (st1 <- st0 && truth(_test)) {
          trace.within(Ghost(Produce(test)), st0) {
            verify(left, rest, ret, post, st1, ctx0)
          }
        }
      }

      for ((_test, st0) <- _test_st) {
        for (st1 <- st0 && !truth(_test)) {
          trace.within(Ghost(Produce(PreOp("!", test))), st0) {
            verify(right, rest, ret, post, st1, ctx0)
          }
        }
      }

    case While(test, spec, body) =>
      val invs = spec collect { case Invariant(assrt) => assrt }
      val inv = And(invs)
      val mod = Syntax.modifies(body)

      for ((_, st1) <- consume(inv, st0.saveOld, ctx0)) {
        val st2 = st1 havoc (mod, ctx0)
        val frame = st2.heap
        for ((_, st3, ctx3) <- produce(inv, st2.pure, ctx0, bind = true)) {
          for ((_test, st4) <- rval_low_test(test, st3, ctx3)) {
            for (st5 <- st4 && truth(_test)) {
              trace.within(body, st5) {
                verify(body, ret, inv, st5, ctx3)
              }
            }

            for (st5 <- st4 && !truth(_test); st6 <- st5 && frame) {
              verify(rest, ret, post, st6, ctx3)
            }
          }
        }
      }

    case _ =>
      throw error.InvalidProgram("unsupported", first)
  }

  def define(first: Def, ctx: Context): Context = first match {
    case TypeDef(typ, name) =>
      ctx copy (typedefs = ctx.typedefs + (name -> typ))

    case StructDecl(name) if ctx.structs contains name =>
      ctx
    case StructDecl(name) =>
      ctx copy (structs = ctx.structs + (name -> None))

    case UnionDecl(name) if ctx.unions contains name =>
      ctx
    case UnionDecl(name) =>
      ctx copy (unions = ctx.unions + (name -> None))

    case EnumDecl(name) if ctx.enums contains name =>
      ctx
    case EnumDecl(name) =>
      ctx copy (enums = ctx.enums + (name -> None))

    case StructDef(name, _) if (ctx.structs contains name) && ctx.structs(name) != None =>
      throw error.InvalidProgram("struct already defined", first)
    case StructDef(name, fields) =>
      ctx copy (structs = ctx.structs + (name -> Some(fields)))

    case UnionDef(name, _) if (ctx.unions contains name) && ctx.unions(name) != None =>
      throw error.InvalidProgram("union already defined", first)
    case UnionDef(name, fields) =>
      ctx copy (unions = ctx.unions + (name -> Some(fields)))

    case EnumDef(Some(name), enum) if (ctx.enums contains name) && ctx.enums(name) != None =>
      throw error.InvalidProgram("enum already defined", first)
    case EnumDef(None, consts) =>
      import secc.pure.toConst
      val add = for ((name, index) <- consts.zipWithIndex)
        yield (Id(name), index: Pure)
      ctx copy (consts = ctx.consts ++ add)
    case EnumDef(Some(name), consts) =>
      val add = for ((name, index) <- consts.zipWithIndex)
        yield (Id(name), index: Pure)
      ctx copy (
        enums = ctx.enums + (name -> Some(consts)),
        consts = ctx.consts ++ add)
  }
}