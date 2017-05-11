package at.logic.gapt.provers.smtlib

import java.io.IOException

import at.logic.gapt.provers.Session._
import at.logic.gapt.provers.IncrementalProver
import at.logic.gapt.utils.{ ExternalProgram, runProcess }
import cats.implicits._
import at.logic.gapt.provers.Session.Runners._

object Z3 extends Z3( "QF_UF" )
class Z3( val logic: String ) extends IncrementalProver with ExternalProgram {

  override def runSession[A]( program: Session[A] ) = {
    val runner = new ExternalSMTLibSessionRunner( "z3", "-smt2", "-in" )
    val result = runner.run( setLogic( logic ) followedBy program )
    runner.process.destroy()

    result
  }

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "z3", "-version" ) )
      true
    } catch {
      case _: IOException => false
    }
}
