package secc.c

object Block {
  def empty = Block(Nil)
}

sealed trait Stmt extends beaver.Symbol {
}

sealed trait Global extends Stmt {
}

sealed trait Def extends Global {
}

case object Malformed extends Stmt {
  def self = this
  override def toString = "/* malformed */"
}

case class Block(stmts: List[Stmt]) extends Stmt {
  def this(stmts: Array[Stmt]) = this(stmts.toList)
  def locals = Set(stmts collect { case VarDef(_, id, _, _) => id }: _*)
  override def toString = stmts.mkString("{", " ", "}")
}

case class Atomic(expr: Expr) extends Stmt {
  override def toString = expr + ";"
}

case class Ghost(aux: Aux) extends Global {
  override def toString = "_(" + aux + ")"
}

case object Break extends Stmt {
  def self = this
  override def toString = "break;"
}

case object Continue extends Stmt {
  def self = this
  override def toString = "continue;"
}

case class Return(expr: Option[Expr]) extends Stmt {
  def this(expr: Expr) = this(Some(expr))
  override def toString = expr match {
    case None => "return;"
    case Some(expr) => "return " + expr + ";"
  }
}

object Return extends (Option[Expr] => Return) {
  val none = Return(None)
}

case class If(test: Expr, left: Stmt, right: Option[Stmt]) extends Stmt {
  def this(test: Expr, left: Stmt) = this(test, left, None)
  def this(test: Expr, left: Stmt, right: Stmt) = this(test, left, Some(right))
  override def toString = right match {
    case None => "if(" + test + ") " + left
    case Some(right) => "if(" + test + ") " + left + " else " + right
  }
}

case class While(test: Expr, specs: List[Spec], body: Stmt) extends Stmt {
  def this(test: Expr, specs: Array[Spec], body: Stmt) = this(test, specs.toList, body)
  override def toString = "while(" + test + ") " + body
}

case class DoWhile(body: Stmt, test: Expr) extends Stmt {
}

case class For(init: Expr, test: Expr, inc: Expr, body: Stmt) extends Stmt {
}

case class TypeDef(typ: Type, name: String) extends Def

case class StructDef(name: String, fields: List[Field]) extends Def {
  def this(name: String, fields: Array[Field]) = this(name, fields.toList)
}

case class UnionDef(name: String, fields: List[Field]) extends Def {
  def this(name: String, fields: Array[Field]) = this(name, fields.toList)
}

case class EnumDef(name: Option[String], cases: List[String]) extends Def {
  def this(cases: Array[String]) = this(None, cases.toList)
  def this(name: String, cases: Array[String]) = this(Some(name), cases.toList)
}

case class StructDecl(name: String) extends Def
case class UnionDecl(name: String) extends Def
case class EnumDecl(name: String) extends Def

case class VarDef(typ: Type, name: Id, init: Option[Expr], specs: List[Spec]) extends Global {
  def this(typ: Type, name: String) = this(typ, Id(name), None, Nil)
  def this(typ: Type, name: String, init: Expr) = this(typ, Id(name), Some(init), Nil)

  def this(typ: Type, name: String, specs: Array[Spec]) = this(typ, Id(name), None, specs.toList)
  def this(typ: Type, name: String, init: Expr, specs: Array[Spec]) = this(typ, Id(name), Some(init), specs.toList)

  override def toString = init match {
    case None => typ + " " + name + ";"
    case Some(init) => typ + " " + name + " = " + init + ";"
  }
}

case class FunDef(ret: Type, name: Id, params: List[Formal], specs: List[Spec], body: Option[Stmt]) extends Global {
  def this(ret: Type, name: String, specs: Array[Spec]) = {
    this(ret, Id(name), Nil, specs.toList, None)
  }

  def this(ret: Type, name: String, specs: Array[Spec], body: Stmt) = {
    this(ret, Id(name), Nil, specs.toList, Some(body))
  }

  def this(ret: Type, name: String, params: Array[Formal], specs: Array[Spec]) = {
    this(ret, Id(name), params.toList, specs.toList, None)
  }

  def this(ret: Type, name: String, params: Array[Formal], specs: Array[Spec], body: Stmt) = {
    this(ret, Id(name), params.toList, specs.toList, Some(body))
  }
}

object Syntax {
  def modifies(expr: Expr): Set[Id] = expr match {
    case _: Id => Set()
    case _: Lit => Set()
    case PreOp("++", id: Id) => Set(id)
    case PreOp("--", id: Id) => Set(id)
    case PostOp("++", id: Id) => Set(id)
    case PostOp("--", id: Id) => Set(id)
    case BinOp("=", id: Id, arg) => Set(id) ++ modifies(arg)
    case PreOp(op, arg) => modifies(arg)
    case PostOp(op, arg) => modifies(arg)
    case BinOp(op, arg1, arg2) => modifies(arg1) ++ modifies(arg2)
    case Index(arg1, arg2) => modifies(arg1) ++ modifies(arg2)
    case Update(arg1, arg2, arg3) => modifies(arg1) ++ modifies(arg2) ++ modifies(arg3)
    case Question(test, left, right) => modifies(test) ++ modifies(left) ++ modifies(right)
    case Cast(typ, expr) => modifies(expr)
    case SizeOfExpr(expr) => Set() // compile time
    case SizeOfType(typ) => Set()
    case Arrow(expr, field) => modifies(expr)
    case Dot(expr, field) => modifies(expr)
    case FunCall(name, args) => Set() ++ (args flatMap modifies)
    case Init(values) => Set() ++ (values flatMap { case (_, expr) => modifies(expr) })
    case Bind(how, params, body) => modifies(body)
    case Old(inner) => modifies(inner)
  }

  def hasEffects(expr: Expr): Boolean = expr match {
    case _: Id => false
    case _: Lit => false
    case PreOp("++", arg) => true
    case PreOp("--", arg) => true
    case PostOp("++", arg) => true
    case PostOp("--", arg) => true
    case BinOp("=", arg1, arg2) => true
    case PreOp(op, arg) => hasEffects(arg)
    case PostOp(op, arg) => hasEffects(arg)
    case BinOp(op, arg1, arg2) => hasEffects(arg1) || hasEffects(arg2)
    case Index(arg1, arg2) => hasEffects(arg1) || hasEffects(arg2)
    case Update(arg1, arg2, arg3) => hasEffects(arg1) || hasEffects(arg2) || hasEffects(arg3)
    case Question(test, left, right) => hasEffects(test) || hasEffects(left) || hasEffects(right)
    case Cast(typ, expr) => hasEffects(expr)
    case SizeOfExpr(expr) => false // compile time
    case SizeOfType(typ) => false
    case Arrow(expr, field) => hasEffects(expr)
    case Dot(expr, field) => hasEffects(expr)
    case FunCall(name, args) => true // XXX: approximation
    case Init(values) => (values exists { case (_, expr) => hasEffects(expr) })
    case Bind(how, params, body) => hasEffects(body)
    case Old(inner) => hasEffects(inner)
  }

  def modifies(stmt: Stmt): Set[Id] = stmt match {
    case _: VarDef => Set()
    case Malformed => Set()
    case Ghost(_) => Set()
    case Atomic(expr) => modifies(expr)
    case Return(None) => Set()
    case Return(Some(expr)) => modifies(expr)
    case Break | Continue => Set()
    case If(test, left, None) => modifies(test) ++ modifies(left)
    case If(test, left, Some(right)) => modifies(test) ++ modifies(left) ++ modifies(right)
    case While(test, invs, body) => modifies(test) ++ modifies(body)
    case DoWhile(body, test) => modifies(test) ++ modifies(body)
    case For(init, test, inc, body) => modifies(init) ++ modifies(test) ++ modifies(inc) ++ modifies(body)
    case Block(stmts) => Set() ++ (stmts flatMap modifies)
    case _: Def | _: FunDef => Set()
  }
}
