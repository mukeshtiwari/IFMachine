package secc.c.test

import secc.c._
import secc.pure._

object Debug {
  def main(args: Array[String]) {
    import Const.nil
    import Sort.list
    import Sort.int

    try {
       Solver.uninterpreted += Fun.mod
      // Solver.timeout = 1000
      val name = "examples/rb-new.c"
      verify(name)
      Console.out.flush()
      Console.err.flush()
    } catch {
      case e: secc.error.Error =>
        Console.out.flush()
        Console.err.flush()
        println(e.info)
        Console.out.flush()
        Console.err.flush()
    }
  }
}
