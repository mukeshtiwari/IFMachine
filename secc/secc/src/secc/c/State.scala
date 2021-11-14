package secc.c


import scala.language.postfixOps

import secc.error
import secc.heap.Heap
import secc.heap.Pred
import secc.heap.Prop
import secc.pure.Pure
import secc.pure.Solver
import secc.pure.Sort
import secc.pure.Relational

case class Box(assrt: Assert, rely: Expr, guarantee: Expr, inst: Store, params: Store) {
  def update(newInst: Store) = copy(inst = newInst filter { case (k,v) => inst contains k })
  override def toString = assrt.toString + " | " + inst.mkString(", ")
}

object Box {
  val empty = Box(True, True, True, Map(), Map())
}

case class State(
  attacker: Pure,
  path: List[Pure],
  store: Store,
  old: List[Store],
  heap: Heap,
  box: Box,
  numAtomicCalls: Int,
  solver: Relational) {

  override def toString = {
    attacker + " | " + store.mkString(", ") + " | " + (path ++ heap.pto ++ heap.chunks).mkString(" && ")
  }

  def info() {
    log.info("state")
    log.shift {
      log.info("store  ", store.mkString(", "))
      log.info("path   ", path.mkString(", "))
      log.info("pto    ", heap.pto.mkString(", "))
      log.info("chunks ", heap.chunks.mkString(", "))
      log.info("shared ", box.toString)
    }
  }

  def saveOld = {
    copy(old = store :: old)
  }

  def high = {
    copy(attacker = secc.pure.High)
  }

  def isPure = {
    heap == Heap.empty
  }

  def pure = {
    copy(heap = Heap.empty)
  }
  
  def updateBox(inst: Store) = {
    copy(box = box update inst)
  }

  def havocBox(ctx: Context): State = {
    val newInst = box.inst map (t => (t._1, ctx arbitrary t._1))
    updateBox(newInst) assign newInst
  }

  def getSolver(relational: Boolean) = {
    if (relational) solver else solver.inner
  }

  def withSolver[A](relational: Boolean)(f: Solver => A): A = {
    // XXX: Note that the non-relational solver cannot deal with Pure.haslabel (and polymorphic types in particular)
    var which = getSolver(relational)

    which scoped {
      which match {
        case which: Relational =>
          which assumeAttacker attacker
        case _ =>

      }

      which assume path

      val ptrs = heap.pto map (_.ptr)

      if (!ptrs.isEmpty) {
        // println(ptrs)
        ptrs foreach {
          _.typ match {
            case Sort.pointer(elem) =>
            case _ => ???
          }
        }
        which assumeDistinct ptrs
      }

      f(which)
    }
  }

  def maybeConsistent: List[State] = {
    withSolver(relational = false) {
      solver =>
        if (solver.isConsistent) List(this)
        else Nil
    }
  }

  def stronglyConsistent: List[State] = {
    withSolver(relational = true) {
      solver =>
        if (solver.isConsistent) List(this)
        else Nil
    }
  }

  def check(phi: Pure): Boolean = {
    withSolver(phi.isRelational) {
      solver => solver isValid phi
    }
  }

  def &&(that: Pure) = {
    copy(path = that :: path) maybeConsistent
  }

  def &&(that: Prop) = {
    copy(heap = heap && that) maybeConsistent
  }

  def &&(that: Heap) = {
    copy(heap = heap && that) maybeConsistent
  }

  def assign(id: Id, arg: Pure) = {
    copy(store = store + (id -> arg))
  }

  def assign(asg: Iterable[(Id, Pure)]) = {
    copy(store = store ++ asg)
  }

  def havoc(id: Id, ctx: Context) = {
    val pair = (id, ctx arbitrary id)
    copy(store = store + pair)
  }

  def havoc(ids: Iterable[Id], ctx: Context) = {
    val pairs = ids map (id => (id, ctx arbitrary id))
    copy(store = store ++ pairs)
  }

  def load(ptr: Pure): (Pure, Pure) = {
    heap load (ptr, solver.isValid) match {
      case None =>
        throw error.VerificationFailure("memory", "illegal dereference", ptr, this)
      case Some((sec, arg)) =>
        (sec, arg)
    }
  }

  def store(ptr: Pure, arg: Pure): (Pure, Pure, State) = {
    heap store (ptr, arg, solver.isValid) match {
      case None =>
        throw error.VerificationFailure("memory", "illegal dereference", ptr, this)
      case Some((sec, old, heap)) =>
        (sec, old, copy(heap = heap))
    }
  }

  def access(ptr: Pure) = {
    val (pto, rest) = heap access (ptr, check)
    pto match {
      case None =>
        throw error.VerificationFailure("memory", "cannot find ", ptr + " |-> ?", this)
      case Some(pto) =>
        (pto, copy(heap = rest))
    }
  }

  def access(pred: Pred, in: List[Pure]) = {
    val (chunk, rest) = heap access (pred, in, check)
    chunk match {
      case None =>
        throw error.VerificationFailure("memory", "cannot find ", pred + "(" + in.mkString(",") + "; ?)", this)
      case Some(chunk) =>
        (chunk, copy(heap = rest))
    }
  }

  def resetAtomicCallCounter(): State = {
    copy (numAtomicCalls = 0)
  }

  def doAtomicCall(): State = {
    if (numAtomicCalls != 0) {
      throw error.VerificationFailure("effects", "multiple atomic calls in same atomic block")
    }
    copy (numAtomicCalls = numAtomicCalls + 1)
  }
}

object State {
  def empty = State(
    attacker = secc.pure.Attacker,
    path = Nil,
    store = Map.empty,
    old = Nil,
    heap = Heap.empty,
    box = Box.empty,
    numAtomicCalls = 0,
    solver = Solver.relational)

  def default = empty
}