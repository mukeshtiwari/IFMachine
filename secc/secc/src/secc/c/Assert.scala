package secc.c

trait Assert extends beaver.Symbol {
  def &&(that: Assert): Assert = (this, that) match {
    case (True, _) => that
    case (False, _) => False
    case (_, True) => this
    case (_, False) => False
    case _ => And(this, that)
  }
  
  def zap(that: Assert): Assert = (this, that) match {
    case (True, _) => that
    case (False, _) => False
    case (_, True) => this
    case (_, False) => False
    case (Exists(bound, body), _) => Exists(bound, body zap that)
    case _ => And(this, that)
  }
}

case class And(left: Assert, right: Assert) extends Assert {
  override def toString = left + " && " + right
}

case class Cond(test: Expr, left: Assert, right: Assert) extends Assert {
  def this(test: Expr, left: Assert) = this(test, left, True)

  override def toString = if (right == True)
    "(" + left + " ==> " + right + ")"
  else
    "(" + test + " ? " + left + " : " + right + ")"
}

object And {
  def apply(args: List[Assert]): Assert = {
    args.foldRight(True: Assert)(_ zap _)
  }

  def apply(args: Array[Assert]): Assert = {
    apply(args.toArray)
  }
}

case class PointsTo(ptr: Expr, sec: Expr, arg: Expr) extends Assert {
  def this(ptr: Expr, arg: Expr) = this(ptr, High, arg)

  // def secs = List(Sec(ptr, sec), Sec(arg, sec))

  override def toString = sec match {
    case High => ptr + " |-> " + arg
    case _ => ptr + " |->[" + sec + "] " + arg
  }
}

case class Chunk(pred: String, in: List[Expr], out: List[Expr]) extends Assert {
  def this(pred: String) = this(pred, Nil, Nil)
  def this(pred: String, in: Array[Expr]) = this(pred, in.toList, Nil)
  def this(pred: String, in: Array[Expr], out: Array[Expr]) = this(pred, in.toList, out.toList)
  override def toString = pred + "(" + in.mkString(", ") + "; " + out.mkString(", ") + ")"
}

case class Exists(params: List[Formal], body: Assert) extends Assert {
  def this(params: Array[Formal], body: Assert) = this(params.toList, body)
  assert(!params.isEmpty)

  def bound = Set(params map (p => Id(p.name)): _*)

  override def toString = {
    params.mkString("exists ", ", ", ". ") + body
  }
}
