package gapt.provers.viper
import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.{instantiate, universalClosure}
import gapt.formats.babel.{Notation, Precedence}
import gapt.logic.hol.skolemize
import gapt.proofs.lk.LKProof
import gapt.proofs.HOLSequent
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.InductiveType
import gapt.provers.OneShotProver
import gapt.provers.escargot.{Escargot, QfUfEscargot}
import gapt.provers.viper.grammars.hSolveQBUP
import gapt.utils.{Maybe, SatMatchers}
import org.specs2.mutable.Specification

class HSolveQbupTest extends Specification with SatMatchers {

  def escargotSmtModNormalize(equations: Seq[Formula]): OneShotProver =
    new OneShotProver {
      val normalizer = Normalizer(equations.map(ReductionRule(_)))

      override def getLKProof(seq: HOLSequent)(implicit ctx: Maybe[MutableContext]): Option[LKProof] =
        throw new NotImplementedError

      override def isValid(seq: HOLSequent)(implicit ctx: Maybe[Context]): Boolean =
        QfUfEscargot.isValid(seq.map(normalizer.normalize(_).asInstanceOf[Formula]))
    }

  "double" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType("nat", hoc"0: nat", hoc"s: nat>nat")
    ctx += hoc"'+': nat>nat>nat"
    ctx += Notation.Infix("+", Precedence.plusMinus)
    ctx += hoc"d: nat>nat"
    val qbup @ Ex(x, qbupMatrix) =
      hof"""
           ∃X (
             ∀n (d 0 = 0 ∧ 0 + 0 = 0 -> X(n, 0)) ∧
             ∀n ∀i (X(n, i) ∧ d(s(i)) = s(s(d(i))) ∧
                    s(i)+s(i) = s(i+s(i)) ∧ i+s(i)=s(i+i)
                -> X(n, s(i))) ∧
             ∀n (X(n, n) -> d(n) = n+n)
           )
         """: @unchecked
    val Some(sol) = hSolveQBUP(qbupMatrix, hof"$x(n, s(0))", QfUfEscargot): @unchecked
    skolemize(BetaReduction.betaNormalize(instantiate(qbup, sol))) must beEValid
  }

  "double mod th" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType("nat", hoc"0: nat", hoc"s: nat>nat")
    ctx += hoc"'+': nat>nat>nat"
    ctx += Notation.Infix("+", Precedence.plusMinus)
    ctx += hoc"d: nat>nat"
    val qbup @ Ex(x, qbupMatrix) =
      hof"""
           ∃X (
             ∀n (d 0 = 0 -> X(n, 0)) ∧
             ∀n ∀i (X(n, i) ∧ d(s(i)) = s(s(d(i))) -> X(n, s(i))) ∧
             ∀n (X(n, n) -> d(n) = n+n)
           )
         """: @unchecked
    val eqTh = Seq(hof"0 + x = x", hof"x + 0 = x", hof"x+s(y)=s(x+y)", hof"s(x)+y=s(x+y)")
    val Some(sol) = hSolveQBUP(qbupMatrix, hof"$x(n, s(0))", escargotSmtModNormalize(eqTh), eqTh): @unchecked
    Escargot.isValid(universalClosure(And(eqTh)) --> BetaReduction.betaNormalize(instantiate(qbup, sol))) must_== true
  }

}
