package at.logic.gapt.integration_tests

import at.logic.gapt.formats.llkNew.ExtendedProofDatabase
import at.logic.gapt.proofs.{ HOLSequent, HOLClause, FOLClause }
import at.logic.gapt.proofs.ceres_omega._
import at.logic.gapt.proofs.lk.{ AtomicExpansion, regularize, LKToLKsk }
import at.logic.gapt.proofs.lkOld.deleteTautologies
import at.logic.gapt.proofs.ceres.CharacteristicClauseSet

import at.logic.gapt.examples.{ nTape, primediv }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkskNew.LKskProof
import at.logic.gapt.proofs.lkskNew.LKskProof.LabelledFormula
import at.logic.gapt.provers.prover9.Prover9
import org.specs2.mutable._
import BetaReduction._

object PDAnalysis extends nTape {
  val pdb = ExtendedProofDatabase( Map( hoa"THEPROOF" -> primediv.proof ), Map(), primediv.defs.asInstanceOf[Map[LambdaExpression, LambdaExpression]] )

  override def proofdb() = pdb;

  override def root_proof() = "THEPROOF";

  // the substitution from the paper. the skolem symbol might be wrong.
  val sub = Substitution( hov"X:nat>o" -> le"\(x:nat) exists z (D z s3 & x < s3 & z > 1)" )

  lazy val css_ : Set[HOLSequent] = {
    def subl( l: LKskProof.Label ) =
      l.map( x => betaNormalize( sub( x ) ) )
    def subf( t: HOLFormula ) =
      betaNormalize( sub( t ) )
    css.map( _.map(
      ( x: LabelledFormula ) => subf( x._2 )
    ) )
  }

  lazy val fol_css_ = css_ map ( _.map( _ match {
    case x: HOLAtom => x
    case x: Any     => throw new Exception( s"$x is not an atom!" )
  } ) )

  lazy val ref = Prover9.getRobinsonProof( fol_css_ )
}

class LNPProofTest extends Specification {

  "The system" should {
    "parse correctly the LNP proof" in {
      PDAnalysis.css_
      //println( PDAnalysis.ref ) //TODO: doesnt work because the set is not first order yet
      ok( "No errors" )
    }

    "parse correctly the LNP proof" in {
      skipped( "doesnt work because the set is not first order yet" )
      PDAnalysis.ref
      ok( "No errors" )
    }
  }

  "prime divisor proof" in { primediv; ok }
}
