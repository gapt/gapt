package at.logic.gapt.provers.smtlib

import java.io.{ BufferedReader, InputStreamReader, PrintWriter }
import java.lang.ProcessBuilder.Redirect

import at.logic.gapt.expr._
import at.logic.gapt.formats.StringInputFile
import at.logic.gapt.formats.lisp._

import scala.collection.mutable

object ExternalSmtlibProgram {
  class UnexpectedTerminationException( input: SExpression )
    extends Exception( s"SMT solver terminated unexpectedly on $input" )
}
