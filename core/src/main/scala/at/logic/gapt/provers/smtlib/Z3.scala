package at.logic.gapt.provers.smtlib

import java.io.IOException

import at.logic.gapt.provers.IncrementalProver
import at.logic.gapt.utils.runProcess
import at.logic.gapt.utils.traits.ExternalProgram

object Z3 extends Z3( "QF_UF" )
class Z3( val logic: String ) extends IncrementalProver with ExternalProgram {

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "z3", "-version" ) )
      true
    } catch {
      case _: IOException => false
    }

  override def startIncrementalSession(): Z3Session = {
    val session = new Z3Session
    session setLogic logic
    session
  }
}

class Z3Session extends ExternalSmtlibProgram {
  override def command = Seq( "z3", "-smt2", "-in" )
}
