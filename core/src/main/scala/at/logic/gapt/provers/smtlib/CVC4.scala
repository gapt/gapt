package at.logic.gapt.provers.smtlib

import java.io.IOException

import at.logic.gapt.provers.Session.Runners.ExternalSMTLibSessionRunner
import at.logic.gapt.provers.IncrementalProver
import at.logic.gapt.provers.Session._
import at.logic.gapt.utils.{ ExternalProgram, runProcess }
import cats.implicits._

object CVC4 extends CVC4( "QF_UF", Seq() )
class CVC4( val logic: String, val extraArgs: Seq[String] = Seq() ) extends IncrementalProver with ExternalProgram {

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "cvc4", "--version" ) )
      true
    } catch {
      case _: IOException => false
    }

  override def runSession[A]( program: Session[A] ) = {
    val runner = new ExternalSMTLibSessionRunner( Seq( "cvc4", "--lang", "smt", "--incremental" ) ++ extraArgs: _* )
    val result = runner.run( setLogic( logic ) followedBy program )
    runner.process.destroy()

    result
  }
}

