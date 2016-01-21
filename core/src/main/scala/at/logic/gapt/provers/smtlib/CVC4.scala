package at.logic.gapt.provers.smtlib

import java.io.IOException

import at.logic.gapt.provers.IncrementalProver
import at.logic.gapt.utils.runProcess
import at.logic.gapt.utils.traits.ExternalProgram

object CVC4 extends CVC4( "QF_UF" )
class CVC4( val logic: String ) extends IncrementalProver with ExternalProgram {

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "cvc4", "--version" ) )
      true
    } catch {
      case _: IOException => false
    }

  override def startIncrementalSession(): CVC4Session = {
    val session = new CVC4Session
    session setLogic logic
    session
  }
}

class CVC4Session extends ExternalSmtlibProgram {
  override def command = Seq( "cvc4", "--lang", "smt", "--incremental" )
}
