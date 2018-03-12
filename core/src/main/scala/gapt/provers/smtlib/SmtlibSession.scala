package gapt.provers.smtlib

import java.io.{ BufferedReader, InputStreamReader, PrintWriter }
import java.lang.ProcessBuilder.Redirect

import gapt.expr._
import gapt.formats.StringInputFile
import gapt.formats.lisp._

import scala.collection.mutable

object ExternalSmtlibProgram {
  class UnexpectedTerminationException( input: SExpression )
    extends Exception( s"SMT solver terminated unexpectedly on $input" )
}
