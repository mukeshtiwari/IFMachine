package secc.c.test

import minitest.SimpleTestSuite
import secc.SecC
import secc.c
import secc.error

object Parser extends SimpleTestSuite {
  for (file <- tests) {
    test(file) {
      try {
        c.parse(file); ()
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