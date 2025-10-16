package gapt.provers.smtlib


import gapt.formats.lisp._


object ExternalSmtlibProgram {
  class UnexpectedTerminationException(input: SExpression)
      extends Exception(s"SMT solver terminated unexpectedly on $input")
}
