/*
 * GAPScalaInteractiveShellLibrary.scala
 *
 */

package at.logic.applet

import at.logic.parsing.language.simple.SimpleHOLParser
import at.logic.parsing.readers.StringReader

import java.io.File.separator
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.util.zip.GZIPInputStream

/* FIXME: Huet's algorithm is not yet adapted to the new lambda calculus
class AppletMain extends java.applet.Applet {
  def huet(s1: String, s2: String) : String = {
    class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

    try {
      HuetAlgorithm.unify1(new MyParser(s1).getTerm(), new MyParser(s2).getTerm()).next match {
        case Some(_) => "Unifiable."
        case None => "Not unifiable."
      }
    }
    catch {
      case e : java.lang.RuntimeException => "RuntimeException (probably parsing error; check input syntax)."
      case e : java.lang.StackOverflowError => "Stack overflow error (i.e. exhausted memory before finding a solution)."
      case _ => "Unkown exception caugt."
    }
  }

  def test() = "scala test!"
}
*/
