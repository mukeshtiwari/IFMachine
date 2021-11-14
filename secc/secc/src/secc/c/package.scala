package secc

import java.io.File
import java.io.FileReader
import java.io.InputStreamReader
import java.io.Reader

import scala.collection.JavaConverters.asScalaBufferConverter

package object c {
  import secc.pure.Pure
  type Store = Map[Id, Pure]

  object Store {
    def apply(ids: Iterable[Id], args: Iterable[Pure]) = {
      val st = (ids zip args)
      st.toMap
    }
  }

  val NULL = Id("NULL")
  val High = Id("high")
  val Low = Id("low")
  val False = Id("false")
  val True = Id("true")
  val TID = Id("TID")

  def verify(code: String) {
    val pos = code.lastIndexOf(":")
    if(pos >= 0) {
      val file = code take (pos)
      val rest = code drop (pos + 1)
      val functions = rest split ','
      verify(file, Some(functions.toList))
    } else {
      val file = code
      verify(file, None)
    }
  }

  def verify(path: String, functions: Option[List[String]]) {
    val stmts = parse(path)
    Verify.functions = functions
    Verify.file(path, stmts)
  }

  def parse(): List[Global] = {
    parse(new InputStreamReader(System.in), "-")
  }

  def parse(path: String): List[Global] = {
    parse(new FileReader(path), path)
  }

  def parse(file: File): List[Global] = {
    parse(new FileReader(file), file.getPath)
  }

  def parse(reader: Reader, path: String): List[Global] = {
    val scanner = new Scanner(reader)
    val parser = new Parser()

    val types = new java.util.HashSet[String]
    val preds = new java.util.HashSet[String]

    types.add("bool")
    types.add("sec")

    scanner.types = types
    scanner.preds = preds

    parser.types = types
    parser.preds = preds

    val result = try {
      parser parse scanner
    } catch {
      case e: Exception =>
        throw error.InvalidProgram("parse", path, e)
    }

    if (result != null) {
      val globals: List[Global] = result.asInstanceOf[java.util.ArrayList[Global]].asScala.toList
      globals
    } else {
      Nil
    }
  }
}