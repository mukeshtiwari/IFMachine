import java.io.FileReader
import java.io.InputStreamReader
import System.in
import collection.JavaConverters._
import java.io.Reader
import java.io.File

package object secc {
  object error {
    abstract class Error extends Exception {
      def info: Seq[Any]
      override def toString = info.mkString(" ")
    }
    
    object Error {
      def unapplySeq(e: Error) = Some(e.info)
    }

    case class InvalidProgram(info: Any*) extends Error
    case class VerificationFailure(info: Any*) extends Error
    case class InternalError(info: Any*) extends Error

    def checkpoint[A](code: => A): A = {
      try {
        code
      } catch {
        case e: InvalidProgram =>
          throw e
        case e: VerificationFailure =>
          throw e
      }
    }
  }

  def assert(prop: Boolean, info: Any*) {
    if (!prop) {
      throw error.InternalError("assertion" +: prop +: info: _*)
    }
  }

  def backtrack() = {
    throw Backtrack()
  }

  case class Backtrack() extends Throwable {
    override def toString = "backtrack"
    override def fillInStackTrace = this
    override val getStackTrace = scala.Array[StackTraceElement]()
  }

  implicit class Control[A](first: => A) {
    def or[B <: A](second: => B) = {
      try {
        first
      } catch {
        case Backtrack() =>
          second
      }
    }
  }

  class Counter(name: String) {
    var count: Long = 0

    def +=(n: Long) {
      count += n
    }
  }

  class Timer(name: String) {
    var prev: Long = 0
    var time: Long = 0

    def start() {
      prev = System.currentTimeMillis
    }

    def stop() {
      time += (System.currentTimeMillis - prev)
    }
  }

  val sub = "₀₁₂₃₄₅₆₇₈₉"
  implicit class StringOps(self: String) {
    def prime = self + "'"

    def __(index: Int): String = {
      self + (index.toString map (n => sub(n - '0')))
    }

    def __(index: Option[Int]): String = index match {
      case None => self
      case Some(index) => this __ index
    }
  }

  implicit class SetOps[A](self: Set[A]) {
    def disjoint(that: Set[A]) = {
      (self & that).isEmpty
    }
  }
}