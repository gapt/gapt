package gapt.integration_tests

import gapt.cutintro._
import gapt.examples.LinearExampleProof
import gapt.expr._
import gapt.expr.formula.fol.Numeral
import gapt.expr.formula.hol.containsQuantifier
import gapt.grammars.DeltaTableMethod
import gapt.logic.Polarity
import gapt.proofs.Sequent
import gapt.proofs.expansion.ETWeakening
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.util.quantRulesNumber
import gapt.proofs.lk.util.weakQuantRulesNumber
import gapt.provers.escargot.Escargot
import org.specs2.mutable._

class CutIntroTest extends Specification {
  "deltatable method" in {
    CutIntroduction( LinearExampleProof( 9 ), method = DeltaTableMethod() ) must beSome
  }

  "maxsat method" in {
    val Some( proof ) = Escargot.getLKProof( hos"!y p(0,y), !x!y (p x (f y) & p x (g y) -> p (s x) y) :- p ${Numeral( 2 )} c" )
    CutIntroduction( proof, method = MaxSATMethod( 1 ) ) must beSome
  }

  "reforest method" in {
    CutIntroduction( LinearExampleProof( 9 ), method = ReforestMethod ) must beSome
  }

  "reforest method with interpolation" in {
    CutIntroduction(
      LinearExampleProof( 24 ),
      method = ReforestMethod, useInterpolation = true ) must beSome
  }

  "linear equality example" in {
    val Some( p ) = Escargot getLKProof hos"!x f (s x) = f x :- f ${Numeral( 9 )} = f 0"
    val Some( q ) = CutIntroduction( p )
    val cutFormulas = q.subProofs collect { case c: CutRule => c.cutFormula } filter { containsQuantifier( _ ) }
    cutFormulas must contain( atMost(
      hof"!x f (s (s (s x))) = f x",
      hof"!x f x = f (s (s (s x)))" ) )
  }

  "linear equality example with interpolation" in {
    val Some( p ) = Escargot.getLKProof( hos"!x f (s x) = f x :- f ${Numeral( 9 )} = f 0" )
    CutIntroduction( p, useInterpolation = true ) must beSome
  }

  "non-prenex proofs" in {
    val Some( expansion ) = Escargot.getExpansionProof( hof"p 0 & !x (p x -> p (s x)) -> p ${Numeral( 9 )}" )
    CutIntroduction( expansion ) must beSome
  }

  "delta table with row merging" in {
    val Some( expansion ) = Escargot getExpansionProof
      hos"""
          p 0, q 0,
          !x (p x -> p (s x)),
          !x (q x -> q (s x))
       :- p ${Numeral( 6 )} & q ${Numeral( 6 )}
      """
    CutIntroduction( expansion, method = DeltaTableMethod( subsumedRowMerging = true ) ) must beLike {
      case Some( lk ) =>
        weakQuantRulesNumber( lk ) must_== ( 2 * 2 + 3 )
    }
  }

  "introduce two cuts into linear example proof with improveSolutionLK" in {
    val us = ( fof"P 0" -> Seq( Seq() ) ) +:
      ( fof"!x (P x -> P (s x))" -> Seq( Seq( fot"x_1" ), Seq( fot"s x_1" ) ) ) +:
      Sequent() :+ ( fof"P ${Numeral( 8 )}" -> Seq( Seq() ) )
    val ss = Seq(
      Seq( fov"x_1" ) -> Seq( Seq( fot"x_2" ), Seq( fot"s (s x_2)" ) ),
      Seq( fov"x_2" ) -> Seq( Seq( fot"0" ), Seq( Numeral( 4 ) ) ) )
    val sehs = SchematicExtendedHerbrandSequent( us, ss )

    val solStruct = SolutionStructure( sehs, CutIntroduction.computeCanonicalSolution( sehs ) )
    val prover = CutIntroduction.BackgroundTheory.PureFOL.prover
    val improved = improveSolutionLK( solStruct, prover, hasEquality = false )
    val pwc = CutIntroduction.buildProofWithCut( improved, prover )

    val cf1 = fof"P x_1 -> P (s (s x_1))"
    val cf2 = fof"P x_2 -> P (s (s (s (s x_2))))"
    improved.formulas must_== Seq( cf1, cf2 )

    quantRulesNumber( pwc ) must_== sehs.size
  }

  "introduce weak quantifiers as low as possible" in {
    val endSequent = hos"!x q(x), q(c)->p(0), !x (p(x)&q(c)->p(s(x))) :- p(${Numeral( 9 )})"
    val Some( proof ) = Escargot.getLKProof( endSequent )
    val Some( proofWithCut ) = CutIntroduction( proof )

    // !x q(x) must only be instantiated once, even though it is used in both branches of the cut.
    proofWithCut.treeLike.postOrder.filter {
      case p: ForallLeftRule => p.mainFormula == hof"!x q(x)"
      case _                 => false
    } must haveSize( 1 )
  }

  "filter bottom during beautification" in {
    val Some( expansion ) = Escargot.getExpansionProof( hos"!x (p x -> p (s x)) :- p 0 -> p ${Numeral( 9 )}" )
    val weirdExpansion = ExpansionProof(
      ETWeakening( hof"!x (p x & -p x)", Polarity.InAntecedent ) +:
        expansion.expansionSequent )
    CutIntroduction.compressToSolutionStructure( weirdExpansion ) must beNone
  }
}

