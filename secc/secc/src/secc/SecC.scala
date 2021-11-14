package secc

import secc.pure.Backend
import secc.pure.Simplify

object SecC {
  var dry: Boolean = false

  def configure(args: List[String]): List[String] = args match {
    case Nil =>
      Nil

    case "-debug:axioms" :: rest =>
      c.log.info("Built-In Axioms")
      c.log.shift {
        for (ax <- pure.axioms) {
          c.log.info(ax)
        }
      }
      configure(rest)
      
    case "-debug:solver" :: rest =>
      Backend.debug = true
      configure(rest)

    case "-debug:simplify" :: rest =>
      Simplify.debug = true
      configure(rest)

    case "-debug" :: rest =>
      c.log.level = c.log.Debug
      configure(rest)

    case "-dry" :: rest =>
      dry = true
      configure(rest)

    case "-no:div" :: rest =>
      import secc.pure.Fun
      import secc.pure.Solver
      Solver.uninterpreted += Fun.divBy
      configure(rest)

    case "-no:mod" :: rest =>
      import secc.pure.Fun
      import secc.pure.Solver
      Solver.uninterpreted += Fun.mod
      configure(rest)

    case "-timeout" :: s :: rest =>
      import secc.pure.Solver
      Solver.timeout = s.toInt
      configure(rest)

    case "-timeout" :: _ =>
      throw new UnsupportedOperationException("-timeout requires an argument")

    case "-solver:oneshot" :: rest =>
      import secc.pure.Solver
      Solver.oneshot = true
      configure(rest)

    case "-solver:incremental" :: rest =>
      import secc.pure.Solver
      Solver.oneshot = false
      configure(rest)

    case file :: rest =>
      file :: configure(rest)
  }

  def main(args: Array[String]) {
    if (args.isEmpty) {
      println("usage: secc [-timeout Nmillisecs] [-debug] [-print_builtin_axioms] file1.c file2.c ...")
    } else {
      /* XXX: unconditionally treat mod as uninterpreted */
      import secc.pure.Fun
      import secc.pure.Solver
      Solver.uninterpreted += Fun.mod
    
      val files = configure(args.toList)
      for (file <- files) {
        try {
          c.log.info(file)
          if (dry)
            c.parse(file)
          else
            c.verify(file)
        } catch {
          case e: java.io.FileNotFoundException =>
            Console.err.println("  file does not exist: " + file)
          case error.InvalidProgram(msg @ _*) =>
            Console.err.println("  invalid program: " + msg.mkString(" "))
          case error.VerificationFailure(msg @ _*) =>
            Console.err.println("  uh oh: " + msg.mkString(" "))
          case e: error.Error =>
            Console.err.println("  uh oh: " + e)
          // ignored on the command line
        }
      }
    }
  }
}