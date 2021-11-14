package secc.pure

case class ProofUnknown(info: Any*) extends secc.error.Error
case class ProofFailure(info: Any*) extends secc.error.Error
case class ProofError(info: Any*) extends secc.error.Error

object Solver {
  var timeout = 5000
  var oneshot = false
  var uninterpreted: Set[Fun] = Set()

  def default = SMT2.z3(timeout)
  def relational = new Relational(default)
  def dummy = new DummySolver
}

class DummySolver extends Solver {
  def assume(phi: Pure) {}
  def assumeDistinct(exprs: Iterable[Pure]) {}
  def push() {}
  def pop() {}
  def isConsistent: Boolean = false
}

trait Solver {
  def assume(phi: Pure)
  def assumeDistinct(exprs: Iterable[Pure])
  def push()
  def pop()

  def isConsistent: Boolean

  def isSatisfiable(phi: Pure): Boolean = {
    assuming(phi) { isConsistent }
  }

  def assume(phis: Iterable[Pure]) {
    for (phi <- phis)
      assume(phi)
  }

  def scoped[A](f: => A): A = {
    push()
    try {
      f
    } finally {
      pop()
    }
  }

  def assuming[A](phis: Pure*)(f: => A): A = scoped {
    assume(phis)
    f
  }

  def isValid(phi: Pure): Boolean = {
    !isSatisfiable(!phi)
  }
}

object Relational {
  val attacker = Var("@attacker", Sort.sec)
}

class Relational(val inner: Solver) extends Solver {
  import Relational.attacker

  def prime(expr: Pure): Pure = expr match {
    case x: Var => x.prime
    case Pure.haslabel(arg, sec) =>
      assert(false, "nested security assertions: " + expr); ???
    case App(fun, args) => App(fun, args map prime)
    case Bind(q, bound, body) => Bind(q, bound map (_.prime), prime(body))
    case _ =>
      assert(false, "unexpected formula to prime" + expr); ???
  }

  def secure(arg: Pure, sec: Pure): Pure = {
    val delta = (sec === prime(sec))
    val phi = (sec lower attacker) ==> (arg === prime(arg))
    delta && phi
  }

  def relational(phi: Pure): Pure =
    if (phi.isRelational) {
      phi match {
        case Pure.haslabel(arg, sec) => secure(arg, sec)
        case Pure.not(arg) => !relational(arg)
        case Pure.and(left, right) => relational(left) && relational(right)
        case Pure.or(left, right) => relational(left) || relational(right)
        case Pure.imp(left, right) => relational(left) ==> relational(right)
        case Pure.eqv(left, right) => relational(left) <=> relational(right)
        case Pure.ite(arg1, arg2, arg3) => {
          assert(arg2.typ == Sort.bool && arg3.typ == Sort.bool);
          relational(arg1) ? (relational(arg2), relational(arg3))
        }
        case Bind(q, bound, body) => {
          val bound_ = bound map (_.prime)
          Bind(q, bound ++ bound_, relational(body))
        }
        case _ => {
          assert(false,"unexpected relational assertion: " + phi)
          ???
        }
      }
    } else {
      phi match {
        case Bind(q, bound, body) =>
          val bound_ = bound map (_.prime)
          Bind(q, bound ++ bound_, body && prime(body))
        case _ => phi && prime(phi)
      }
    }
    

  def assumeAttacker(level: Pure) {
    inner.assume(attacker === level)
  }

  def assume(phi: Pure) {
    // if (phi.free.isEmpty) {
    //   inner.assume(phi)
    // } else {
      inner.assume(relational(phi))
    // }
  }

  def assumeDistinct(exprs: Iterable[Pure]) {
    inner.assumeDistinct(exprs)
    inner.assumeDistinct(exprs map prime)
  }

  def push() { inner.push() }
  def pop() { inner.pop() }
  def isConsistent: Boolean = inner.isConsistent
}