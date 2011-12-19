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
  import at.logic.language.hol._
  import at.logic.language.fol._
  import at.logic.calculi.lk.base.types.FSequent
  import at.logic.calculi.lk.base.FSequent
  import at.logic.calculi.lk.base._
  import at.logic.calculi.lksk.base._
  import at.logic.language.hol.logicSymbols._
  import at.logic.transformations.skolemization.skolemize
  import at.logic.algorithms.lk.regularize
  import ceresHelp.{apply => ceresHelp}

  println("Welcome to the GAPT shell!")
  println("See ceresHelp for the commands.")"""

  def main(args: Array[String]) {
    val f = File.createTempFile("cli-script", ".scala")
    f.deleteOnExit()
    val w = new BufferedWriter( new FileWriter(f) )
    w.write(script)
    w.close
    MainGenericRunner.main(Array("-usejavacp", "-i", f.getAbsolutePath))
    sys.exit(0)
  }
}
