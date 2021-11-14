package secc.c

sealed trait Expr extends Assert {
}

case class Field(typ: Type, name: String, ghost: Boolean) extends beaver.Symbol {
  override def toString = typ + " " + name
}

case class Formal(typ: Type, name: String) extends beaver.Symbol {
  def pair = (Id(name), typ)
  override def toString = typ + " " + name
}

case class Lit(arg: Any) extends Expr {
  override def toString = arg.toString
}

case class Id(name: String) extends Expr {
  override def toString = name
}

object Id {
  val result = Id("result")
  val main = Id("main")
}

case class PreOp(op: String, arg: Expr) extends Expr {
  override def toString = "(" + op + " " + arg + ")"
}

case class PostOp(op: String, arg: Expr) extends Expr {
  override def toString = "(" + arg + " " + op + ")"
}

case class BinOp(op: String, arg1: Expr, arg2: Expr) extends Expr {
  override def toString = "(" + arg1 + " " + op + " " + arg2 + ")"
}

case class Index(base: Expr, index: Expr) extends Expr {
  override def toString = base + "[" + index + "]"
}

case class Update(base: Expr, index: Expr, arg: Expr) extends Expr {
  override def toString = base + "[" + index + ":=" + arg + "]"
}

case class Question(test: Expr, left: Expr, right: Expr) extends Expr {
  override def toString = "(" + test + " ? " + left + " : " + right + ")"
}

case class SizeOfType(typ: Type) extends Expr {
  def free = Set()
  override def toString = "sizeof(" + typ + ")"
}

case class SizeOfExpr(expr: Expr) extends Expr {
  override def toString = "sizeof(" + expr + ")"
}

case class Cast(typ: Type, expr: Expr) extends Expr {
  override def toString = "(" + typ + ")" + expr
}

case class Dot(expr: Expr, field: String) extends Expr {
  override def toString = expr + "." + field
}

case class Arrow(expr: Expr, field: String) extends Expr {
  override def toString = expr + "->" + field
}

case class FunCall(fun: Id, args: List[Expr]) extends Expr { // no function pointers
  def this(name: String, args: Array[Expr]) = this(Id(name), args.toList)
  override def toString = fun + args.mkString("(", ", ", ")")
}

case class Init(values: List[(Option[String], Expr)]) extends Expr { // { .field = value } or { value }
}

case class Old(inner: Expr) extends Expr {
  override def toString = "old(" + inner + ")"
}

object Post {
  def apply(expr: Expr, ids: Set[Id]): Expr = expr match {
    case id: Id => if (ids contains id) id else Old(id)
    case _: Lit => expr
    case PreOp(op, arg) => PreOp(op, Post(arg, ids))
    case PostOp(op, arg) => PostOp(op, Post(arg, ids))
    case BinOp(op, arg1, arg2) => BinOp(op, Post(arg1, ids), Post(arg2, ids))
    case Index(base, index) => Index(Post(base, ids), Post(index, ids))
    case Update(base, index, arg) => Update(Post(base, ids), Post(index, ids), Post(arg, ids))
    case Question(test, left, right) => Question(Post(test, ids), Post(left, ids), Post(right, ids))
    case Cast(typ, expr) => Cast(typ, Post(expr, ids))
    case SizeOfExpr(expr) => expr
    case SizeOfType(typ) => expr
    case Arrow(expr, field) => Arrow(Post(expr, ids), field)
    case Dot(expr, field) => Dot(Post(expr, ids), field)
    case FunCall(name, args) => FunCall(name, args map (Post(_, ids)))
    case Init(values) => Init(values map { case (name, expr) => (name, Post(expr, ids)) })
    case bind @ Bind(how, params, body) => Bind(how, params, Post(body, ids ++ bind.bound))
    case Old(inner) => ???
  }

  def apply(assrt: Assert, ids: Set[Id]): Assert = assrt match {
    case expr: Expr => Post(expr, ids)
    case And(left, right) => And(Post(left, ids), Post(right, ids))
    case Cond(test, left, right) => Cond(Post(test, ids: Set[Id]), Post(left, ids), Post(right, ids))
    case PointsTo(ptr, sec, arg) => PointsTo(Post(ptr, ids), Post(sec, ids), Post(arg, ids))
    case Chunk(pred, in, out) => Chunk(pred, in map (Post(_, ids)), out map (Post(_, ids)))
    case bind @ Exists(params, body) => Exists(params, Post(body, ids ++ bind.bound))
  }
}

case class Bind(how: String, params: List[Formal], body: Expr) extends Expr {
  def this(how: String, params: Array[Formal], body: Expr) = this(how, params.toList, body)

  def bound = Set(params map (p => Id(p.name)): _*)

  override def toString = {
    how + params.mkString(" ", ", ", ". ") + body
  }
}

