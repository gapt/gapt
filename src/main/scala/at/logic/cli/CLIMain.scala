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

  val script = """  
  import at.logic.cli.GAPScalaInteractiveShellLibrary._
  import at.logic.language.lambda.types._
  import at.logic.language._
  import at.logic.language.hol._
  import at.logic.language.fol._
  import at.logic.calculi.lk._
  import at.logic.calculi.lk.base._
  import at.logic.calculi.lksk
  import at.logic.language.lambda.symbols._
  import at.logic.language.hol.logicSymbols._
  import at.logic.language.hoare._
  import at.logic.transformations.skolemization.skolemize
  import at.logic.algorithms.lk.regularize
  import at.logic.calculi.occurrences.FormulaOccurrence
  import at.logic.algorithms.cutIntroduction.Deltas._
  import at.logic.algorithms.lk.statistics._
  import at.logic.provers.minisat.MiniSATProver
  import at.logic.gui.prooftool.gui.{Main => PT}
  import help.{apply => help}
  import at.logic.cli.GPL.{apply => copying, printLicense => license}

  println()
  println("    *************************************")
  println("    *    Welcome to the GAPT shell!     *")
  println("    *  See help for a list of commands. *")
  println("    *************************************")
  println()
  println(" GAPT Copyright (C) 2014")
  println(" This program comes with ABSOLUTELY NO WARRANTY. This is free")
  println(" software, and you are welcome to redistribute it under certain")
  println(" conditions; type `copying' for details.")
  println()
  """

  def main(args: Array[String]) {
    val f = File.createTempFile("cli-script", ".scala")
    f.deleteOnExit()
    val w = new BufferedWriter( new FileWriter(f) )
    w.write(script)
    w.close
    MainGenericRunner.main(Array("-usejavacp","-i",f.getCanonicalPath, "-Yrepl-sync"))
    sys.exit(0)
  }
}
