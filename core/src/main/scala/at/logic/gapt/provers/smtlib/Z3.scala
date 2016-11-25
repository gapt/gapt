package at.logic.gapt.provers.smtlib

import java.io.IOException

import at.logic.gapt.provers.Session._
import at.logic.gapt.provers.IncrementalProver
import at.logic.gapt.utils.{ ExternalProgram, runProcess }
import cats.implicits._
import at.logic.gapt.provers.Session.Compilers._

object Z3 extends Z3( "QF_UF" )
class Z3( val logic: String ) extends IncrementalProver with ExternalProgram {

  override def runSession[A]( program: Session[A] ) = {
    val p = for {
      _ <- setLogic( logic )
      result <- program
      _ <- close
    } yield result

    val compiler = new ExternalSMTLibSessionCompiler {
      override def command = Seq( "z3", "-smt2", "-in" )
    }

    p.foldMap( compiler )
  }
  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "z3", "-version" ) )
      true
    } catch {
      case _: IOException => false
    }
}
