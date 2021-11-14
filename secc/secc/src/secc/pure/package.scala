package secc

package object pure {
  val sub = "₀₁₂₃₄₅₆₇₈₉"

  type TRen = Map[Param, Param]

  type Typing = Map[Param, Sort]
  object Typing { val empty: Typing = Map() }

  type Ren = Map[Var, Var]
  object Ren { val empty: Ren = Map() }

  type Subst = Map[Var, Pure]
  object Subst { val empty: Subst = Map() }

  val True = Fun._true()
  val False = Fun._false()

  val High = Fun.high()
  val Low = Fun.low()
  val Attacker = Fun.attacker()

  val Tid = Fun.tid()

  val l = Var("l", Sort.sec)
  val l0 = Var("l", Sort.sec, Some(0))
  val l1 = Var("l", Sort.sec, Some(1))
  val l2 = Var("l", Sort.sec, Some(2))

  val axioms = List(
    Low !== High,

    Attacker !== High,

    Tid > toConst(0),

    // partial order
    All(
      Set(l),
      l lower l),
    All(
      Set(l0, l1),
      ((l0 lower l1) && (l1 lower l0)) ==> (l0 === l1)),
    All(
      Set(l0, l1, l2),
      ((l0 lower l1) && (l1 lower l2)) ==> (l0 lower l2)),

    // top and bottom
    All(
      Set(l),
      l lower High),
    All(
      Set(l),
      Low lower l))

  implicit def toConst(n: Int) = Const.int(n)

  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None => self
      case Some(index) => this __ index
    }

    def form(args: List[_]): String = {
      var as = args
      val res = new StringBuilder
      for (c <- self) {
        if (c == '_') {
          res append as.head
          as = as.tail
        } else {
          res append c
        }
      }
      assert(as.isEmpty)
      res.toString
    }
  }

  implicit class SetOps[A](self: Set[A]) {
    def disjoint(that: Set[A]) = {
      (self & that).isEmpty
    }
  }

}