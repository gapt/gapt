package at.logic.gapt.proofs.sketch

import at.logic.gapt.expr.{ FOLAtom, HOLAtom, freeVariables }
import at.logic.gapt.proofs.{ FOLClause, OccConnector, SequentProof }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.{ findDerivationViaResolution, mapInputClauses }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.escargot.Escargot

import scala.collection.mutable
import scalaz._
import Scalaz._

/**
 * Intermediate data structure intendend for the proof replay in the TPTP proof import.
 *
 * A refutation sketch is a list of clauses, where each clause is either an axiom (that occurs in the CNF of the
 * original end-sequent) or is a first-order consequence of previous ones.
 *
 * These two cases are modelled as [[SketchAxiom]] and [[SketchInference]].
 */
sealed trait RefutationSketch extends SequentProof[FOLAtom, RefutationSketch] {
  override def occConnectors = immediateSubProofs map { p => OccConnector( conclusion, p.conclusion, p.conclusion map { _ => Seq() } ) }
  override def mainIndices = Seq()
  override def auxIndices = immediateSubProofs map { _ => Seq() }
}

/**
 * Axiom in a refutation sketch.
 *
 * The clause [[axiom]] occurs as a clause in the CNF of the end-sequent we're proving.
 *
 * @param axiom  Clause of the CNF.
 */
case class SketchAxiom( axiom: FOLClause ) extends RefutationSketch {
  override def conclusion = axiom
  override def immediateSubProofs: Seq[RefutationSketch] = Seq()
}

/**
 * Inference in a refutation sketch.
 *
 * The clause [[from]] should be a first-order consequence of the conclusions of [[from]].
 *
 * This rule corresponds to a line in a TPTP proof which just indicates the previous lines from which it follows,
 * but does not specify the precise inference rule employed.
 *
 * @param conclusion  Conclusion of the inference.
 * @param from  Premises of the inference.
 */
case class SketchInference( conclusion: FOLClause, from: Seq[RefutationSketch] ) extends RefutationSketch {
  override def immediateSubProofs = from

  override def productArity = 1 + from.size
  override def productElement( n: Int ) = if ( n == 0 ) conclusion else from( n - 1 )
}

case class SketchSplit(
    splittingClause: RefutationSketch, part1: FOLClause,
    case1: RefutationSketch, case2: RefutationSketch
) extends RefutationSketch {
  require( part1 isSubMultisetOf splittingClause.conclusion )
  val part2 = splittingClause.conclusion diff part1

  require( case1.conclusion.isEmpty )
  require( case2.conclusion.isEmpty )

  val addAxioms1 = Set( part1 )

  val groundNegPart1 = part1.filter( freeVariables( _ ).isEmpty ).map( FOLClause() :+ _, _ +: FOLClause() ).elements
  val addAxioms2 = Set( part2 ) ++ groundNegPart1

  override def immediateSubProofs = Seq( splittingClause, case1, case2 )
  override def conclusion = FOLClause()
}

case class UnprovableSketchInference( inference: SketchInference )

object RefutationSketchToRobinson {
  /**
   * Converts a refutation sketch to a resolution proof.
   *
   * Each [[SketchInference]] is replaced by a resolution derivation that is obtained
   * using the provided resolution prover.
   *
   * @param sketch  Refutation sketch to convert.
   * @param prover  Resolution prover used to reconstruct the inferences.
   * @return  <code>Some(proof)</code> if all inferences could be reconstructed, <code>None</code> otherwise.
   */
  def apply( sketch: RefutationSketch, prover: ResolutionProver = Escargot ): ValidationNel[UnprovableSketchInference, ResolutionProof] = {
    type ErrorOr[X] = ValidationNel[UnprovableSketchInference, X]
    val memo = mutable.Map[RefutationSketch, ErrorOr[ResolutionProof]]()
    def solve( s: RefutationSketch ): ErrorOr[ResolutionProof] = memo.getOrElseUpdate( s, s match {
      case SketchAxiom( axiom ) => Success( Input( axiom ) )
      case s @ SketchInference( conclusion, from ) =>
        import Validation.FlatMap._
        for {
          solvedFrom <- Applicative[ErrorOr].traverse( from.toList )( solve )
          solvedFromMap = solvedFrom.map { p => p.conclusion -> p }.toMap
          deriv <- findDerivationViaResolution( s.conclusion, solvedFromMap.keySet.map( _.map( _.asInstanceOf[HOLAtom] ) ), prover ).
            map { _.success }.
            getOrElse { UnprovableSketchInference( s ).failureNel }
        } yield mapInputClauses( deriv )( solvedFromMap )
      case s: SketchSplit =>
        import Validation.FlatMap._
        //        for {
        //          splittingClause <- solve( s.splittingClause )
        //          case1 <- solve( s.case1 )
        //          case2 <- solve( s.case2 )
        //        } yield Splitting( splittingClause, s.part1, s.part2, case1, case2 )
        // FIXME
        ???
    } )
    solve( sketch ) map { simplifyResolutionProof( _ ) }
  }
}
