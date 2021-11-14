package secc.c

import secc.error

sealed trait Aux extends beaver.Symbol {
}

case class Internal(info: String, f: (State, Context) => List[(State, Context)]) extends Aux {
  override def toString = "internal " + info
}

case class Produce(assrt: Assert) extends Aux {
  override def toString = "assume " + assrt
}

case class Consume(assrt: Assert, msg: String) extends Aux {
  override def toString = msg match {
    case "assert" => "assert " + assrt
    case _ => "assert " + assrt + " \"" + msg + "\""
  }
}

case class Unfold(assrt: Assert) extends Aux {
  override def toString = "unfold " + assrt
}

case class Fold(assrt: Assert) extends Aux {
  override def toString = "fold " + assrt
}

case object BeginAtomicBlock extends Aux {
  def self = this

  override def toString = "atomic begin"
}

case object EndAtomicBlock extends Aux {
  def self = this

  override def toString = "atomic end"
}

case class Apply(stmt: Stmt) extends Aux {
  override def toString = "apply " + stmt
}

case class ApplyForall(generalize: List[Formal], stmt: FunCall) extends Aux {
  def this(generalize: Array[Formal], stmt: FunCall) = this(generalize.toList, stmt)
  override def toString = "apply forall " + generalize.mkString(", ") + ". " + stmt
}

case object Prune extends Aux {
  def self = this

  override def toString = "prune"
}

case class Rules(exprs: List[Expr], smt: Boolean) extends Aux {
  def this(exprs: Array[Expr], smt: Boolean) = this(exprs.toList, smt)

  override def toString = if (smt) {
    exprs.mkString("axioms ", "; ", ";")
  } else {
    exprs.mkString("rewrites ", "; ", ";")
  }
}

case class Lemma(expr: Expr, induct: Option[Id]) extends Aux {
  def this(expr: Expr) = this(expr, None)
  def this(expr: Expr, id: Id) = this(expr, Some(id))

  override def toString = induct match {
    case None => "lemma " + expr
    case Some(id) => "lemma " + expr + " induct " + id
  }
}

sealed trait Spec extends beaver.Symbol {
}

case class Requires(pre: Assert) extends Spec {
  override def toString = "requires " + pre
}

case class Ensures(post: Assert) extends Spec {
  override def toString = "ensures " + post
}

case class Invariant(inv: Assert) extends Spec {
  override def toString = "invariant " + inv
}

case class Resource(inv: Assert) extends Spec {
  override def toString = "resource " + inv
}

case class Maintains(assrt: Assert) extends Spec {
  override def toString = "maintains " + assrt
}

case class Fails(msg: String) extends Spec {
  override def toString = "fails " + msg
}

case object Lemma extends Spec {
  def self = this

  override def toString = "lemma"
}

case object PureSpec extends Spec {
  def self = this

  override def toString = "pure"
}

case object AtomicSpec extends Spec {
  def self = this

  override def toString = "atomic"
}

case class Shared(assrt: Assert, rely: Expr, guarantee: Expr) extends Spec {
  override def toString = "shared " + assrt + " rely " + rely + " guarantee " + guarantee
}

case class PredDef(name: String, in: List[Formal], out: List[Formal], body: Option[Assert]) extends Aux {
  def this(name: String) = this(name, Nil, Nil, None)
  def this(name: String, body: Assert) = this(name, Nil, Nil, Some(body))
  def this(name: String, in: Array[Formal]) = this(name, in.toList, Nil, None)
  def this(name: String, in: Array[Formal], body: Assert) = this(name, in.toList, Nil, Some(body))
  def this(name: String, in: Array[Formal], out: Array[Formal]) = this(name, in.toList, out.toList, None)
  def this(name: String, in: Array[Formal], out: Array[Formal], body: Assert) = this(name, in.toList, out.toList, Some(body))

  override def toString = body match {
    case None => "predicate " + name + "(" + in.mkString(", ") + "; " + out.mkString(", ") + ")"
    case Some(body) => "predicate " + name + "(" + in.mkString(", ") + "; " + out.mkString(", ") + ")" + " " + body
  }
}

case class PureDef(name: String, in: List[Formal], out: Type, body: Option[Expr]) extends Aux {
  def this(name: String, out: Type) = this(name, Nil, out, None)
  def this(name: String, out: Type, body: Expr) = this(name, Nil, out, Some(body))
  def this(name: String, in: Array[Formal], out: Type) = this(name, in.toList, out, None)
  def this(name: String, in: Array[Formal], out: Type, body: Expr) = this(name, in.toList, out, Some(body))

  override def toString = (in, body) match {
    case (Nil, None) => "constant " + out + " " + name
    case (Nil, Some(body)) => "constant " + out + " " + name + "(" + in.mkString(", ") + ")" + " = " + body
    case (_, None) => "function " + out + " " + name + "(" + in.mkString(", ") + ")"
    case (_, Some(body)) => "function " + out + " " + name + "(" + in.mkString(", ") + ")" + " = " + body
  }
}

case class Prepost(pre: List[Assert], post: List[Assert], fails: List[String], shared: Option[Shared],
  isLemma: Boolean, isAtomic: Boolean, isPure: Boolean) {
}

object Prepost {
  def apply(specs: List[Spec]): Prepost = {
    val pre = specs collect {
      case Requires(pre) => pre
      case Maintains(pre) => pre
    }

    val post = specs collect {
      case Ensures(post) => post
      case Maintains(post) => post
    }

    val fails = specs collect {
      case Fails(msg) => msg
    }

    val shared = specs collect {
      case s @ (Shared(_, _, _)) => s
    } match {
      case Nil => None
      case List(shared) => Some(shared)
      case _ =>
        throw error.InvalidProgram("at most one shared block is allowed per function")
    }

    val isLemma = specs contains Lemma
    val isAtomic = specs contains AtomicSpec
    val isPure = specs contains PureSpec

    Prepost(pre, post, fails, shared, isLemma, isAtomic, isPure)
  }
}
