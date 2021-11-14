package secc.c.test

import minitest.SimpleTestSuite
import secc.SecC
import secc.c
import secc.error
import secc.pure.Solver
import secc.pure.Fun

object Examples extends SimpleTestSuite {
  for (file <- tests) {
    test(file) {
      try {
        c.Verify.interactive = false // get exceptions
        /* XXX: mod unconditionally uninterpreted */
        Solver.uninterpreted = Set(Fun.mod)

        c.verify(file)
      } catch {
        case e: error.Error =>
          println(e.info)
          throw e
      }
    }
  }

  def main(args: Array[String]) {
  }
}