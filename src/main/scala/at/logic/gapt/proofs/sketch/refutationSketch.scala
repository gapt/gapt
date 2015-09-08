package at.logic.gapt.proofs.sketch

import at.logic.gapt.expr.{ FOLAtom, FOLFormula, Eq }
import at.logic.gapt.expr.fol.{ FOLMatchingAlgorithm, FOLSubstitution }
import at.logic.gapt.expr.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.gapt.proofs.resolution.robinson.RobinsonResolutionProof
import at.logic.gapt.proofs.resolution.{ FOLClause, HOLClause }
import at.logic.gapt.proofs.resolutionNew._
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.resolutionNew.{ mapInputClauses, resNew2Old, findDerivationViaResolution }
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

object RefutationSketch {
  sealed abstract class Justification
  case object Axiom extends Justification
  case class Inference( from: Seq[Int] ) extends Justification
  case object ArbitraryInference extends Justification

  case class Step( clause: FOLClause, justification: Justification )
}
case class RefutationSketch( steps: Seq[RefutationSketch.Step] )

object RefutationSketchToRobinson extends Logger {
  import RefutationSketch._

  def apply( sketch: RefutationSketch ): Option[RobinsonResolutionProof] = applyNew( sketch ) map { resNew2Old( _ ) }

  def applyNew( sketch: RefutationSketch ): Option[ResolutionProof] = {
    val solvedSteps = mutable.Map[FOLClause, ResolutionProof]()
    sketch.steps foreach {
      case Step( step, _ ) if solvedSteps.contains( step ) => ()
      case Step( step, Axiom ) =>
        solvedSteps.update( step, InputClause( step ) )
      case Step( step, justification ) =>
        debug( s"Proving $step" )
        val relevantPrevSteps = justification match {
          case Inference( from )  => from.map( sketch.steps( _ ) ).map( _.clause ).toSet
          case ArbitraryInference => solvedSteps.keys.toSet
        }
        findDerivationViaResolution.applyNew( step, relevantPrevSteps ) match {
          case Some( deriv ) =>
            val filledInDeriv = mapInputClauses( deriv ) { other =>
              relevantPrevSteps.view.flatMap {
                case prevStep =>
                  // the prover9 interface and hence findDerivationViaResolution doesn't use the variables from the passed CNF...
                  FOLMatchingAlgorithm.matchTerms( prevStep.toFormula.asInstanceOf[FOLFormula], other.toFormula.asInstanceOf[FOLFormula] ) map { subst =>
                    Instance( solvedSteps( prevStep ), subst )
                  }
              }.head
            }
            require( filledInDeriv.conclusion isSubMultisetOf step )
            solvedSteps.update( step, filledInDeriv )
          case None =>
            warn( s"Could not derive $step" )
        }
    }
    solvedSteps.get( FOLClause() )
  }
}