package gapt.provers.smtlib

import gapt.expr._
import gapt.formats.lisp.{LFun, LList, LSymbol, SExpression}
import org.specs2.mutable._
import gapt.provers.Session._
import cats.implicits._
import gapt.expr.formula.Atom
import gapt.expr.ty.TBase
import gapt.expr.ty.To
import gapt.utils.EitherHelpers._

class Z3SessionTest extends Specification {

  if (!Z3.isInstalled) skipAll

  "check sat of empty theory" in {
    Z3.runSession(checkSat) must_== Right(true)
  }

  "validity of linear example" in {
    val nat = TBase("nat")
    val o = Const("0", nat)
    val s = Const("s", nat ->: nat)
    val p = Const("p", nat ->: To)

    val numeral = LazyList.iterate[Expr](o)(s(_))

    val n = 10

    val getUnsatCore = ask(LFun("get-unsat-core")) map {
      e =>
        (e: @unchecked) match {
          case LList(labels @ _*) =>
            labels map { e => (e: @unchecked) match { case LSymbol(l) => l } }
        }
    }

    val session: Session[(Boolean, Boolean, Seq[String])] = for {
      _ <- setOption("produce-unsat-cores", "true")
      _ <- declareSymbolsIn(o, s, p)
      _ <- assert(Atom(p(o)))
      _ <- (0 until (2 * n)).toList.map(i => (p(numeral(i)) --> p(numeral(i + 1)), s"hyp$i")).traverse_(p => assert(p._1, p._2))
      p <- withScope {
        for {
          _ <- assert(-p(numeral(n)))
          sat <- checkSat
          labels <- getUnsatCore
        } yield (sat.get, labels)
      }
      satOuter <- checkSat
    } yield (p._1, satOuter.get, p._2)

    val (satInner, satOuter, labels) = Z3.runSession(session)

    satInner must_== false
    satOuter must_== true
    labels must contain(exactly(0 until n map { i => s"hyp$i" }: _*))
  }
}
