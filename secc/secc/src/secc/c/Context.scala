package secc.c

import secc.error
import secc.heap.Pred
import secc.pure.Fun
import secc.pure.Pure
import secc.pure.Rewrite
import secc.pure.Param
import secc.pure.Sort
import secc.pure.Var
import secc.heap.Offset
import secc.pure.App

sealed trait Mode {
  // TODO: implement this and use
  def checkRead(id: Id): Boolean = ???
  def checkWrite(id: Id): Boolean = ???
  def checkLoad(): Boolean = ???
  def checkLoad(typ: Sort, field: String): Boolean = ???
  def checkStore(): Boolean = ???
  def checkStore(typ: Sort, field: String): Boolean = ???
}

object Mode {
  case object ghost extends Mode
  case object pure extends Mode
  case object normal extends Mode
  case object atomic extends Mode
  // case object readonly extends Mode
}

sealed trait TypedefSort { def name: String }
sealed trait StructSort { def name: String }
sealed trait UnionSort { def name: String }

/**
 * This class represents the context of the symbolic execution that includes definitions and scopes.
 *
 * Note that since all definitions in C can be scoped inside inner functions,
 * type and function definitions are considered to be dynamic.
 */
case class Context(
  /** C type definitions */
  typedefs: Map[String, Type],
  structs: Map[String, Option[List[Field]]],
  unions: Map[String, Option[List[Field]]],
  enums: Map[String, Option[List[String]]],

  /** global and local C variables */
  vars: Map[Id, Type],

  /** numeric constants defined by enums */
  consts: Map[Id, Pure],

  /** C functions */
  funs: Map[Id, (Type, List[Formal], Option[Stmt])],

  /** specification annotations of variables and functions */
  specs: Map[Id, List[Spec]],

  /** Types of ghost variables */
  ghost: Map[Id, Type],

  /** logic functions and spatial predicates */
  sig: Map[String, Fun],
  axioms: List[Pure],
  rewrites: List[Rewrite],

  preds: Map[String, Pred],
  defs: Map[String, (List[Id], List[Id], Assert)],

  void: Sort,
  bool: Sort,
  int: Sort,
  char: Sort,
  sec: Sort,

  modes: List[Mode]) {

  import Eval._

  def mode = modes.head
  def isInAtomicMode = mode == Mode.atomic
  def isInGhostMode = mode == Mode.ghost
  def isInNormalMode = mode == Mode.normal
  def isInPureMode = mode == Mode.pure
  def isInPureOrGhostMode = isInPureMode || isInGhostMode

  def defaultState = {
    val st = State.default
    // st assume axioms
    st
  }

  def checkRead(id: Id) = mode match {
    case Mode.ghost | Mode.pure =>
      if (!(vars contains id) && !(ghost contains id))
        throw error.InvalidProgram("cannot access: " + id, "undeclared identifier", "current mode: " + mode)
    case Mode.normal | Mode.atomic =>
      if (!(vars contains id)) {
        if (ghost contains id)
          throw error.VerificationFailure("effects", "cannot access ghost state " + id, "current mode: " + mode)
        else
          throw error.InvalidProgram("cannot access: " + id, "undeclared identifier", "current mode: " + mode)
      }
  }

  def checkWrite(id: Id) = mode match {
    case Mode.ghost | Mode.pure =>
      if (!(ghost contains id)) {
        if (vars contains id)
          throw error.VerificationFailure("effects", "cannot modify program state " + id, "current mode: " + mode)
        else
          throw error.InvalidProgram("cannot modify: " + id, "undeclared identifier", "current mode: " + mode)
      }
    case Mode.normal | Mode.atomic =>
      if (!(vars contains id)) {
        if (ghost contains id)
          throw error.VerificationFailure("effects", "cannot modify ghost state " + id, "current mode: " + mode)
        else
          throw error.InvalidProgram("cannot modify: " + id, "undeclared identifier", "current mode: " + mode)
      }
  }

  def checkStore() = mode match {
    case Mode.pure =>
      throw error.VerificationFailure("effects", "cannot access the heap", "current mode: " + mode)
    case Mode.atomic =>
      throw error.VerificationFailure("effects", "cannot write non-atomically", "current mode: " + mode)
    case Mode.ghost =>
      throw error.VerificationFailure("effects", "can store to ghost-fields only", "current mode: " + mode)
    case Mode.normal =>
    // ok
  }

  def checkStore(typ: Sort, field: String): Unit = mode match {
    case Mode.pure =>
      throw error.VerificationFailure("effects", "cannot access the heap", "current mode: " + mode)
    case Mode.atomic =>
      throw error.VerificationFailure("effects", "cannot store non-atomically", "current mode: " + mode)
    case Mode.ghost | Mode.normal =>
      // TODO: lemmas should not be allowed to have effects at all... lemma mode or multiple ghost modes?
      typ match {
        case Sort.pointer(elem: StructSort) =>
          structs(elem.name).get.find(_.name == field) match {
            case Some(Field(_, _, ghost)) if ghost && !isInGhostMode =>
              throw error.VerificationFailure("memory", "storing to ghost field from non-ghost mode")
            case Some(Field(_, _, ghost)) if !ghost && isInGhostMode =>
              throw error.VerificationFailure("memory", "storing to non-ghost field from ghost mode")
            case _ =>
            // ok
          }
        case _ =>
          checkStore()
      }
    // TODO: disallow unions that involve (nested) ghost fields (in structs)
  }

  def checkLoad() = mode match {
    case Mode.pure =>
      throw error.VerificationFailure("effects", "cannot access the heap", "current mode: " + mode)
    case Mode.atomic =>
      throw error.VerificationFailure("effects", "cannot read non-atomically", "current mode: " + mode)
    case Mode.normal | Mode.ghost =>
    // OK
  }

  def checkLoad(typ: Sort, field: String): Unit = mode match {
    case Mode.pure =>
      throw error.VerificationFailure("effects", "cannot access the heap", "current mode: " + mode)
    case Mode.atomic =>
      throw error.VerificationFailure("effects", "cannot load non-atomically", "current mode: " + mode)
    case Mode.ghost | Mode.normal =>
      typ match {
        case Sort.pointer(elem: StructSort) =>
          structs(elem.name).get.find(_.name == field) match {
            case Some(Field(_, _, ghost)) if ghost && !isInGhostMode =>
              throw error.VerificationFailure("memory", "loading from ghost field from non-ghost mode")
            case _ =>
            // ok
          }
        case _ =>
          checkLoad()
      }
  }

  def checkCall(expr: FunCall, isLemma: Boolean, isAtomic: Boolean, isPure: Boolean) = mode match {
    case Mode.pure if !isLemma =>
      throw error.VerificationFailure("effects", "cannot call non-lemma function", expr, "current mode: " + mode)
    case Mode.pure if !isPure =>
      throw error.VerificationFailure("effects", "cannot call non-pure lemma function", expr, "current mode: " + mode)
    case Mode.pure =>
    // ok to call lemma
    case Mode.ghost if !isLemma =>
      throw error.VerificationFailure("effects", "cannot call non-lemma function", expr, "current mode: " + mode)
    case Mode.ghost if isAtomic =>
      throw error.VerificationFailure("effects", "cannot call atomic function", expr, "current mode: " + mode)
    case Mode.ghost =>
    // ok to call lemma
    case Mode.normal if isAtomic =>
      throw error.VerificationFailure("effects", "cannot call atomic function", expr, "current mode: " + mode)
    case Mode.normal if isLemma =>
      throw error.VerificationFailure("effects", "cannot call lemma", expr, "current mode: " + mode)
    case Mode.normal =>
    // ok to call non-atomic functions
    case Mode.atomic if !isAtomic =>
      throw error.VerificationFailure("effects", "cannot call non-atomic function", expr, "current mode: " + mode)
    case Mode.atomic if isLemma =>
      throw error.VerificationFailure("effects", "cannot call lemma", expr, "current mode: " + mode)
    case Mode.atomic =>
    // ok to call atomic function
  }

  def enter(mode: Mode) = {
    copy(modes = mode :: modes)
  }

  def leave() = {
    copy(modes = modes.tail)
  }

  def declareGhost(params: List[(Id, Type)]) = {
    copy(ghost = ghost ++ params)
  }

  def declareGhost(id: Id, typ: Type) = {
    copy(ghost = ghost + (id -> typ))
  }

  def declare(id: Id, typ: Type) = mode match {
    case Mode.ghost | Mode.pure =>
      copy(ghost = ghost + (id -> typ))
    case Mode.normal | Mode.atomic =>
      //      if (typ.isLogical)
      //        throw error.VerificationFailure("effects", "logic type for program variable", (id, typ), "current mode: " + mode)
      copy(vars = vars + (id -> typ))
  }

  def declare(params: List[(Id, Type)]) = mode match {
    case Mode.ghost | Mode.pure =>
      copy(ghost = ghost ++ params)
    case Mode.normal | Mode.atomic =>
      //      val lts = params filter (_._2.isLogical)
      //      if (!lts.isEmpty)
      //        throw error.VerificationFailure("effects", "logic type for program variable", lts.mkString(", "), "current mode: " + mode)
      copy(vars = vars ++ params)
  }

  def arbitrary(id: Id, typ: Type): Var = {
    Var.fresh(id.name, resolve(typ))
  }

  def arbitrary(param: Formal): (Id, Var) = {
    val Formal(typ, name) = param
    val id = Id(name)
    (id, arbitrary(id, typ))
  }

  def arbitrary(id: Id): Var = {
    checkWrite(id)

    if (vars contains id)
      return Var.fresh(id.name, resolve(vars(id)))
    if (ghost contains id)
      return Var.fresh(id.name, resolve(ghost(id)))

    throw error.InternalError("unknown checked identifier", id)
  }

  def predicate(name: String, in: List[Formal], out: List[Formal], body: Option[Assert]) = {
    val _in = in map { case Formal(typ, name) => resolve(typ) }
    val _out = out map { case Formal(typ, name) => resolve(typ) }
    val pred = Pred(name, _in, _out)
    body match {
      case None =>
        copy(preds = preds + (name -> pred))
      case Some(body) =>
        val xin = in map { case Formal(typ, name) => Id(name) }
        val xout = out map { case Formal(typ, name) => Id(name) }
        copy(preds = preds + (name -> pred), defs = defs + (name -> (xin, xout, body)))
    }
  }

  def function(name: String, in: List[Formal], out: Type, body: Option[Expr]) = {
    val _in = in map { case Formal(typ, name) => Var(name, resolve(typ)) }
    val xin = in map { case Formal(typ, name) => Id(name) }
    val res = resolve(out)
    val args = _in map (_.typ)
    val fun = Fun(name, args, res)
    body match {
      case None =>
        copy(sig = sig + (name -> fun))
      case Some(body) =>
        val env = Store(xin, _in)
        // Note: no recursive functions
        // - eval will fail because the function is not yet defined
        // - otherwise eval would recurse forever
        val rw = Rewrite(App(fun, _in), eval(body, env, Nil, this))
        copy(sig = sig + (name -> fun), rewrites = rw :: rewrites)
    }
  }

  def index(ptr: Pure, index: Pure) = {
    val fun = Offset.index(ptr)
    fun(ptr, index)
  }

  def resolve(fields: List[Field], how: String, ptr: Pure, field: String): Pure = fields.find(_.name == field) match {
    case Some(Field(typ, _, _)) =>
      val res = resolve(typ)
      val fun = how match {
        case "->" => Offset.arrow(ptr, field, res)
        case "." => Offset.dot(ptr, field, res)
      }
      fun(ptr)
    case _ =>
      throw error.InvalidProgram("no such field", fields, ptr + "->" + field)
  }

  def resolve(what: String, where: Map[String, Option[List[Field]]], name: String, how: String, ptr: Pure, field: String): Pure = {
    if (!(where contains name))
      throw error.InvalidProgram("undeclared " + what, name, ptr + how + field)

    val fields = where(name).getOrElse {
      throw error.InvalidProgram("undefined " + what, name, ptr + how + field)
    }

    resolve(fields, how, ptr, field)
  }

  def dot(base: Pure, field: String): Pure = {
    val sort = base.typ
    resolve(".", sort, base, field)
  }

  def arrow(ptr: Pure, field: String): Pure = ptr.typ match {
    case Sort.pointer(elem) =>
      resolve("->", elem, ptr, field)
    case _ =>
      throw error.InvalidProgram("not a pointer to struct or union", ptr, ptr + "->" + field)
  }

  def resolve(how: String, sort: Sort, ptr: Pure, field: String): Pure = sort match {
    case sort: StructSort =>
      resolve("struct", structs, sort.name, how, ptr, field)

    case sort: UnionSort =>
      resolve("union", unions, sort.name, how, ptr, field)

    case sort: TypedefSort =>
      val name = sort.name
      if (!(typedefs contains name))
        throw error.InvalidProgram("undeclared type", name, ptr + how + field)

      typedefs(name) match {
        case AnonStruct(fields) =>
          resolve(fields, how, ptr, field)
        case AnonUnion(fields) =>
          resolve(fields, how, ptr, field)
        case _ =>
          throw error.InvalidProgram("not a pointer to struct or union", ptr, ptr + how + field)
      }

    case _ =>
      throw error.InvalidProgram("not a pointer to struct or union", ptr, ptr + how + field)
  }

  def resolve(typ: Type): Sort = {
    resolve(None, typ)
  }

  def resolve(name: Option[TypeName], typ: Type): Sort = typ match {
    case Void => void
    case SignedInt => int
    case SignedChar => char
    case TypedefName("sec") => sec
    case TypedefName("bool") => bool
    case PtrType(elem) => Sort.pointer(resolve(elem))

    case Type.param(name) => Param(name)
    case Type.list(elem) => Sort.list(resolve(elem))
    case Type.array(dom, ran) => Sort.array(resolve(dom), resolve(ran))

    case typ @ TypedefName(name) =>
      // Note: pick last name in the chain to get foo for typedef struct { ... } foo;
      if (!(typedefs contains name))
        throw error.InvalidProgram("cannot resolve name of undefined type", typ)
      resolve(Some(typ), typedefs(name))

    case _: EnumName => Sort.int
    case StructName(name) => new Sort.base(name) with StructSort
    case UnionName(name) => new Sort.base(name) with UnionSort

    case _: CompoundType =>
      name match {
        case None => throw error.InvalidProgram("cannot resolve name of anonymous type", typ)
        case Some(name) => new Sort.base(name.name) with TypedefSort
      }
  }

}

object Context {
  val empty = Context(
    typedefs = Map(),
    structs = Map(),
    unions = Map(),
    enums = Map(),

    vars = Map(),
    consts = Map(
      TID -> Fun.tid()),
    funs = Map(),

    specs = Map(),
    ghost = Map(),

    sig = Map(),
    axioms = List(),
    rewrites = List(),

    preds = Map(),
    defs = Map(),

    void = Sort.unit,
    bool = Sort.bool,
    int = Sort.int,
    char = Sort.int,
    sec = Sort.sec,

    modes = Nil)

  val default = empty copy (
    sig = Map(
      "true" -> Fun._true,
      "false" -> Fun._false,
      "low" -> Fun.low,
      "high" -> Fun.high,
      "attacker" -> Fun.attacker,
      "+" -> Fun.plus,
      "-" -> Fun.minus,
      "*" -> Fun.times,
      "/" -> Fun.divBy,
      "%" -> Fun.mod,
      "<" -> Fun.lt,
      "<=" -> Fun.le,
      "⊑" -> Fun.lower,
      ">" -> Fun.gt,
      ">=" -> Fun.ge,
      "!" -> Fun.not,
      "&&" -> Fun.and,
      "||" -> Fun.or,
      "==>" -> Fun.imp,
      "<=>" -> Fun.eqv,

      "null" -> Fun._null,
      "true" -> Fun._true,
      "false" -> Fun._false,

      "nil" -> Fun.nil,
      "cons" -> Fun.cons,
      "in" -> Fun.in,
      "head" -> Fun.head,
      "tail" -> Fun.tail,
      "last" -> Fun.last,
      "init" -> Fun.init,

      "select" -> Fun.select,
      "store" -> Fun.store),

    axioms = secc.pure.axioms,

    modes = List(Mode.normal))
}
