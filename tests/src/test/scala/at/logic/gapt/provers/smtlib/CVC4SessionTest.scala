package at.logic.gapt.provers.smtlib

import at.logic.gapt.expr._
import at.logic.gapt.formats.lisp.{ LAtom, LFun, LList }
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.provers.Session._
import cats.implicits._
import org.specs2.mutable._

class CVC4SessionTest extends Specification {

  if ( !CVC4.isInstalled ) skipAll

  "check sat of empty theory" in {
    CVC4.runSession( checkSat ) must_== true
  }

  "push and pop" in {
    implicit var ctx = Context()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"p: nat>o"

    CVC4.runSession {
      for {
        _ <- declareSymbolsIn( ctx.constants )
        _ <- assert( hof"p 0 -> -p (s 0)" )
        sat1 <- withScope { assert( hof"p 0 & p (s 0)" ) >> checkSat }
        sat2 <- checkSat
        sat3 <- withScope { assert( hof"p 0 & 0 = s 0" ) >> checkSat }
      } yield ( sat1, sat2, sat3 )
    } must_== ( false, true, false )
  }
}
