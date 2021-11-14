import mill._
import mill.scalalib._

object secc extends ScalaModule {
    def scalaVersion = "2.13.2"
    def mainClass = Some("secc.SecC")
    def unmanagedClasspath = T {
        if (!ammonite.ops.exists(millSourcePath / "lib")) Agg()
        else Agg.from(ammonite.ops.ls(millSourcePath / "lib").map(PathRef(_)))
    }

    object test extends Tests {
        def ivyDeps = Agg(ivy"io.monix::minitest:2.7.0")
        def testFrameworks = Seq("minitest.runner.Framework")
        def unmanagedClasspath = secc.unmanagedClasspath
    }
}
