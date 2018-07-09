package gapt.provers.smtlib

import java.io.IOException

import gapt.provers.Session.Runners.ExternalSMTLibSessionRunner
import gapt.provers.IncrementalProver
import gapt.provers.Session._
import gapt.utils.{ ExternalProgram, runProcess }
import cats.implicits._

object CVC4 extends CVC4( "QF_UF", Seq(), treatUnknownAsSat = false )
class CVC4( val logic: String, val extraArgs: Seq[String] = Seq(),
            override val treatUnknownAsSat: Boolean = false ) extends IncrementalProver with ExternalProgram {

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "cvc4", "--version" ) )
      true
    } catch {
      case _: IOException => false
    }

  override def runSession[A]( program: Session[A] ) = {
    val runner = new ExternalSMTLibSessionRunner( Seq( "cvc4", "--lang", "smt", "--incremental" ) ++ extraArgs: _* )
    val result = runner.run( setLogic( logic ) *> program )
    runner.process.destroy()

    result
  }
}

