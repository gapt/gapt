package at.logic.gapt.provers.smtlib

import java.io.IOException

import at.logic.gapt.provers.Session.Compilers.ExternalSMTLibSessionCompiler
import at.logic.gapt.provers.IncrementalProver
import at.logic.gapt.provers.Session._
import at.logic.gapt.utils.{ ExternalProgram, runProcess }

object CVC4 extends CVC4( "QF_UF" )
class CVC4( val logic: String ) extends IncrementalProver with ExternalProgram {

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "cvc4", "--version" ) )
      true
    } catch {
      case _: IOException => false
    }

  override def runSession[A]( program: Session[A] ) = {
    val p = wrap( setLogic( logic ), close )( program )

    p.foldMap( new ExternalSMTLibSessionCompiler {
      override def command = Seq( "cvc4", "--lang", "smt", "--incremental" )
    } )
  }
}

