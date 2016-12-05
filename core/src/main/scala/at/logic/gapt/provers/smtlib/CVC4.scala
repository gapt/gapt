package at.logic.gapt.provers.smtlib

import java.io.IOException

import at.logic.gapt.provers.Session.Runners.ExternalSMTLibSessionRunner
import at.logic.gapt.provers.IncrementalProver
import at.logic.gapt.provers.Session._
import at.logic.gapt.utils.{ ExternalProgram, runProcess }

import scalaz._
import Scalaz._

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
    val runner = new ExternalSMTLibSessionRunner( "cvc4", "--lang", "smt", "--incremental" )
    val result = runner.run( setLogic( logic ) >> program )
    runner.process.destroy()

    result
  }
}

