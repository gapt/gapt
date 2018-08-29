package gapt.proofs.reduction

import gapt.expr._
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.Sort
import gapt.proofs.expansion.ETAtom
import gapt.proofs.expansion.ETWeakQuantifier
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.resolution.Input
import gapt.proofs.resolution.MguResolution
import gapt.proofs.resolution.eliminateSplitting
import gapt.provers.escargot.Escargot
import gapt.provers.smtlib.Z3
import gapt.utils.SatMatchers
import org.specs2.mutable._

class ErasureReductionTest extends Specification with SatMatchers {
  "two-sorted" in {
    implicit var ctx = Context()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += Sort( "witness" )
    ctx += hoc"f: witness > witness"
    ctx += hoc"P: nat > witness > o"
    ctx += hoc"Q: nat > o"

    val red = new ErasureReductionHelper( ctx.constants.toSet )

    val c1 = Clause() :+ hoa"P 0 y"
    val c2 = hoa"P x (f y)" +: Clause() :+ hoa"P (s x) y"
    val c3 = hoa"P x y" +: Clause() :+ hoa"Q x"
    val c4 = hoa"Q (s (s (s (s 0))))" +: Clause()

    val Seq( ec1, ec2, ec3, ec4 ) = Seq( c1, c2, c3, c4 ) map { red.forward }

    val p1 = Input( ec2 )
    val p2 = MguResolution( p1, Suc( 0 ), p1, Ant( 0 ) )
    val p3 = MguResolution( p2, Suc( 0 ), p2, Ant( 0 ) )
    val p4 = MguResolution( Input( ec1 ), Suc( 0 ), p3, Ant( 0 ) )
    val p5 = MguResolution( Input( ec3 ), Suc( 0 ), Input( ec4 ), Ant( 0 ) )
    val p6 = MguResolution( p4, Suc( 0 ), p5, Ant( 0 ) )

    p6.conclusion must_== Clause()

    val reifiedProof = red.back( p6, Set( c1, c2, c3, c4 ) )
    reifiedProof.conclusion must_== Clause()
  }

  "variables as weak quantifier instances" in {
    implicit var ctx = Context()
    ctx += Sort( "foo" )
    ctx += hoc"P: foo>o"

    val sequent = hof"∀x P x" +: Sequent() :+ hof"∃x P x"

    val red = new ErasureReductionHelper( ctx.constants.toSet )

    val deepAtom = red.forward( hof"P z", Map( hov"z: foo" -> FOLVar( "z" ) ) ).asInstanceOf[FOLAtom]
    val firstOrderEP =
      ExpansionProof(
        ETWeakQuantifier(
          red.forward( hof"∀x P x", Map() ),
          Map( FOLVar( "z" ) -> ETAtom( deepAtom, Polarity.InAntecedent ) ) ) +:
          Sequent()
          :+ ETWeakQuantifier(
            red.forward( hof"∃x P x", Map() ),
            Map( FOLVar( "z" ) -> ETAtom( deepAtom, Polarity.InSuccedent ) ) ) )

    red.back( firstOrderEP, sequent ).deep must beValidSequent
  }

  "strong quantifiers" in {
    Escargot.withDeskolemization.extendToManySortedViaErasure.
      getExpansionProof( hof"!x P(x:nat) -> !x P(x)" ).
      get.deep must beEValidSequent
    ok
  }
}

class ReductionTest extends Specification {
  "many-sorted lambda" in {
    val sequent = hos"∀f P(f) = f(c: nat) :- P(λx h(h(x))) = h(h(c))"

    "resolution" in {
      val reduction =
        LambdaEliminationReductionRes() |>
          HOFunctionReductionRes() |>
          CNFReductionResRes |>
          // PredicateReductionCNF |>
          ErasureReductionCNF

      val ( folCNF, back ) = reduction.forward( sequent )

      val Some( folProof ) = Escargot.getResolutionProof( folCNF )

      val proof = back( eliminateSplitting( folProof ) )
      proof.subProofs foreach {
        case Input( Sequent( Seq( conj ), Seq() ) )  => conj must_== sequent.succedent.head
        case Input( Sequent( Seq(), Seq( axiom ) ) ) => axiom must_== sequent.antecedent.head
        case Input( _ )                              => ko
        case _                                       => ok
      }
      ok
    }

    "expansion" in {
      val reduction =
        LambdaEliminationReductionET() |>
          HOFunctionReductionET() |>
          // PredicateReductionET |>
          ErasureReductionET

      val ( folSequent, back ) = reduction.forward( sequent )

      val Some( folProof ) = Escargot.getExpansionProof( folSequent )

      val proof = back( folProof )
      proof.shallow must_== sequent

      val reductionForChecking =
        LambdaEliminationReduction() |>
          HOFunctionReduction()
      val ( tffDeep, _ ) = reductionForChecking.forward( proof.deep )

      Escargot isValid tffDeep must_== true

      val z3WithQuantifiers = new Z3( "UF" )
      if ( !z3WithQuantifiers.isInstalled ) skipped
      z3WithQuantifiers.isValid( tffDeep ) must_== true
    }

  }
}
