package gapt.provers.sat

import java.io.IOException

import gapt.formats.dimacs._
import gapt.utils.{ExternalProgram, runProcess, withTempFile}
import os._
import gapt.expr.formula.Top

class ExternalSATSolver(val command: String*) extends SATSolver with ExternalProgram {
  protected def runProgram(dimacsInput: String): Option[String] =
    withTempFile.fromString(dimacsInput) { dimacsInputFile =>
      withTempFile { dimacsOutputFile =>
        runProcess.withExitValue(command ++ Seq(dimacsInputFile.toString, dimacsOutputFile.toString)) match {
          case (10, _) => /* SAT */ Some(read(dimacsOutputFile))
          case (20, _) => /* UNSAT */ None
          case (_, str) =>
            throw new Exception(s"Error executing external sat prover $command:\n$str")
        }
      }
    }

  override def solve(cnf: DIMACS.CNF): Option[DIMACS.Model] =
    runProgram(writeDIMACS(cnf)) map { readDIMACS(_) }

  override val isInstalled: Boolean =
    try solve(Top()).isDefined
    catch { case _: IOException => false }

  override def toString: String = {
    val commandString: String = command map { c => "\"" + c + "\"" } mkString ", "
    s"ExternalSATSolver($commandString)"
  }
}

object MiniSAT extends ExternalSATSolver("minisat")
