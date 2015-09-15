package at.logic.gapt.proofs.sketch

import at.logic.gapt.expr.{ FOLAtom, FOLFormula }
import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.proofs.lkNew.OccConnector
import at.logic.gapt.proofs.{ SequentProof, FOLClause }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.{ mapInputClauses, findDerivationViaResolution }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

trait RefutationSketch extends SequentProof[FOLAtom, RefutationSketch] {
  override def occConnectors = immediateSubProofs map { p => OccConnector( conclusion, p.conclusion, p.conclusion map { _ => Seq() } ) }
  override def mainIndices = Seq()
  override def auxIndices = immediateSubProofs map { _ => Seq() }
}

case class SketchAxiom( axiom: FOLClause ) extends RefutationSketch {
  override def conclusion = axiom
  override def immediateSubProofs: Seq[RefutationSketch] = Seq()
}

case class SketchInference( conclusion: FOLClause, from: Seq[RefutationSketch] ) extends RefutationSketch {
  override def immediateSubProofs = from

  override protected def stepString( subProofLabels: Map[Any, String] ) =
    s"$conclusion    (SketchInference(${from map subProofLabels mkString ", "})"
}

object RefutationSketchToRobinson extends Logger {
  def apply( sketch: RefutationSketch, prover: ResolutionProver ): Option[ResolutionProof] = {
    val memo = mutable.Map[RefutationSketch, Option[ResolutionProof]]()
    def solve( s: RefutationSketch ): Option[ResolutionProof] = memo.getOrElseUpdate( s, s match {
      case SketchAxiom( axiom ) => Some( InputClause( axiom ) )
      case SketchInference( conclusion, from ) =>
        debug( s"Proving $conclusion" )
        val solvedFrom = from.flatMap { c => solve( c ) map { sol => c.conclusion -> sol } }.toMap
        findDerivationViaResolution( conclusion, solvedFrom.keySet, prover ) map { deriv =>
          val filledInDeriv = mapInputClauses( deriv ) { other =>
            solvedFrom.view.flatMap {
              case ( prevStep, solution ) =>
                // the prover9 interface and hence findDerivationViaResolution doesn't use the variables from the passed CNF...
                FOLMatchingAlgorithm.matchTerms( prevStep.toFormula.asInstanceOf[FOLFormula], other.toFormula.asInstanceOf[FOLFormula] ) map { subst =>
                  Instance( solution, subst )
                }
            }.head
          }
          require( filledInDeriv.conclusion isSubMultisetOf conclusion )
          filledInDeriv
        } orElse {
          warn( s"Could not derive $conclusion" )
          None
        }
    } )
    solve( sketch ) map { simplifyResolutionProof( _ ) }
  }
}