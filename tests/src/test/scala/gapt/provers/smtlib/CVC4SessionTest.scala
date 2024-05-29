package gapt.provers.smtlib

import gapt.expr._
import gapt.formats.lisp.{LFun, LList, LSymbol}
import gapt.proofs.context.update.InductiveType
import gapt.provers.Session._
import cats.implicits._
import gapt.proofs.context.Context
import org.specs2.mutable._

class CVC4SessionTest extends Specification {

  if (!CVC4.isInstalled) skipAll

  "check sat of empty theory" in {
    CVC4.runSession(checkSat) must_== Right(true)
  }

  "push and pop" in {
    implicit var ctx = Context()
    ctx += InductiveType("nat", hoc"0: nat", hoc"s: nat>nat")
    ctx += hoc"p: nat>o"

    CVC4.runSession {
      for {
        _ <- declareSymbolsIn(ctx.constants)
        _ <- assert(hof"p 0 -> -p (s 0)")
        sat1 <- withScope { assert(hof"p 0 & p (s 0)") *> checkSat }
        sat2 <- checkSat
        sat3 <- withScope { assert(hof"p 0 & 0 = s 0") *> checkSat }
      } yield (sat1, sat2, sat3)
    } must_== (Right(false), Right(true), Right(false))
  }
}
