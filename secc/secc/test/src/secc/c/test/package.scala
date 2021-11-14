package secc.c

import java.io.File

package object test {
  val dirs = List(
    "examples/regression",
    "examples/data-structures",
    "examples/case-studies")

  val tests = for (dir <- dirs;
                   file <- new File(dir).list())
    yield dir + "/" + file
}
