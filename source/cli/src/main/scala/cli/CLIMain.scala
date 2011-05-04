/*
 * GAPScalaInteractiveShellLibrary.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.cli

import scala.tools.nsc.MainGenericRunner
import at.logic.cli.GAPScalaInteractiveShellLibrary._
import at.logic.language.fol._
import java.io._

object CLIMain {

  val script = """import at.logic.cli.GAPScalaInteractiveShellLibrary._
  import at.logic.language.fol._

  println("Welcome to the GAPT shell!")
  println("See ceresHelp() for the commands.")"""

  def main(args: Array[String]) {
    val f = File.createTempFile("cli-script", ".scala")
    f.deleteOnExit()
    val w = new BufferedWriter( new FileWriter(f) )
    w.write(script)
    w.close
    MainGenericRunner.main(Array("-usejavacp", "-i", f.getAbsolutePath))
    exit(0)
  }
}
