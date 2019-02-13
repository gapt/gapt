package gapt.integration_tests

import gapt.formats.llk.ExtendedProofDatabase
import gapt.proofs.{ FOLClause, HOLClause, HOLSequent }
import gapt.proofs.ceres_omega._
import gapt.proofs.ceres.{ CharacteristicClauseSet, deleteTautologies }
import gapt.examples.primediv
import gapt.expr._
import gapt.provers.prover9.Prover9
import org.specs2.mutable._
import BetaReduction._
import gapt.expr.subst.Substitution
import gapt.proofs.lk.util.regularize

object PDAnalysis extends AnalysisWithCeresOmega {
  val pdb = ExtendedProofDatabase( Map( hoa"THEPROOF" -> primediv.proof ), Map(), primediv.ctx.definitions )

  override def proofdb() = pdb;

  override def root_proof() = "THEPROOF";

  // the substitution from the paper. the skolem symbol might be wrong.
  val sub = Substitution( hov"X:nat>o" -> le"^(x:nat) ?(z:nat) (D z (s_1 : nat) & x < (s_1 : nat) & z > (1:nat))" )

  lazy val css_ : Set[HOLSequent] = {
    def subf( t: Formula ) =
      betaNormalize( sub( t ) )
    css.map( _.map( subf ) )
  }

  lazy val fol_css_ = css_ map ( _.map( _ match {
    case x: Atom => x
    case x: Any  => throw new Exception( s"$x is not an atom!" )
  } ) )

  lazy val ref = Prover9.getResolutionProof( fol_css_ )
}

class LNPProofTest extends Specification {

  "The system" should {
    "parse correctly the LNP proof" in {
      PDAnalysis.css_
      // println( PDAnalysis.css_ )
      ok( "No errors" )
    }

    "refutation" in {
      skipped( "doesnt work because the set is not first order yet" )
      PDAnalysis.ref
      ok( "No errors" )
    }
  }

  "prime divisor proof" in { primediv; ok }
}
