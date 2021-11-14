package secc.c

import secc.pure.Pure
import secc.error

import scala.util.DynamicVariable

sealed trait Trace

import secc.pure

object trace extends DynamicVariable(Nil: List[(Stmt, State)]) {
  case class VerificationFailure(trace: List[(Stmt, State)], info: Any*) extends error.Error
  def debug(tr: List[(Stmt, State)]): Unit = tr match {
    case Nil =>
    case (stmt, st) :: rest =>
      log.debug(stmt)
      debug(rest)
  }
  
  def within[A](aux: Aux, st: State)(f: => A): A = {
    within(Ghost(aux), st)(f)
  }

  def within[A](stmt: Stmt, st: State)(f: => A): A = {
    val old = value
    value = (stmt, st) :: old

    try {
      f
    } catch {
      case e: Throwable =>
        log.debug("error trace")
        log.shift {
          debug(value)
        }
        e match {
          case error.VerificationFailure(info @ _*) =>
            throw trace.VerificationFailure(value, info: _*)
          case pure.ProofUnknown(info @ _*) =>
            throw trace.VerificationFailure(value, info: _*)
          case _ =>
            throw e
        }
    } finally {
      value = old
    }
  }
}

object log extends DynamicVariable(0) {
  val Debug = 3
  val Info = 2
  val Error = 1
  val Quiet = 0

  var level = Info

  def indent = "  " * value

  def print(how: Int, nl: Boolean, args: Any*) {
    val text = args.mkString(indent, " ", "")
    if (level >= how) {
      if (nl) Console.println(text)
      else Console.print(text)
    }
  }

  def debug_(args: Any*) {
    print(Debug, false, args: _*)
  }

  def info_(args: Any*) {
    print(Info, false, args: _*)
  }

  def error_(args: Any*) {
    print(Error, false, args: _*)
  }

  def debug(args: Any*) {
    print(Debug, true, args: _*)
  }

  def info(args: Any*) {
    print(Info, true, args: _*)
  }

  def error(args: Any*) {
    print(Error, true, args: _*)
  }

  def shift[A](f: => A): A = {
    withValue(value + 1)(f)
  }
}