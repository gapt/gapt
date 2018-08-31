package gapt.provers.viper.aip

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.InductiveType
import gapt.proofs.lk.LKProof
import gapt.provers.viper.aip.axioms.GeneralInductionAxioms
import org.specs2.mutable.Specification

class GeneralInductionAxiomsTest extends Specification {

  implicit var ctx = MutableContext.default()
  ctx += InductiveType( "nat", hoc"0:nat", hoc"s:nat>nat" )
  ctx += hoc"P:nat>nat>o"

  val axiomFactory = GeneralInductionAxioms()
  val axioms = axiomFactory.apply( Sequent() :+ ( "" -> hof"P(a,b)" ) )

  val formulas = axioms match {
    case Right( list ) => list map {
      _.formula
    }
  }
  val proofs: List[LKProof] = axioms match {
    case Right( list ) => list map {
      _.proof
    }
  }

  "induction axioms should be as expected" in {
    formulas mustEqual List(
      hof"(⊤ ⊃ ∀b P(0:nat, b:nat)) ∧ ∀a_0 (∀b P(a_0, b) ⊃ ∀b P(s(a_0), b)) ⊃ ∀a ∀b P(a, b)",
      hof"(⊤ ⊃ ∀a P(a:nat, 0:nat)) ∧ ∀b_0 (∀a P(a, b_0) ⊃ ∀a P(a, s(b_0))) ⊃ ∀b ∀a P(a, b)" )
  }

  "induction axioms should be proved" in {
    proofs( 0 ).conclusion mustEqual Sequent() :+ formulas( 0 )
    proofs( 1 ).conclusion mustEqual Sequent() :+ formulas( 1 )
  }
}
