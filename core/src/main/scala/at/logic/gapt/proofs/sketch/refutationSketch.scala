package at.logic.gapt.proofs.sketch

import at.logic.gapt.expr.{ FOLAtom, HOLAtom, clauseSubsumption }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.{ FOLClause, HOLClause, OccConnector, SequentProof }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.escargot.{ Escargot, NonSplittingEscargot }
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable
import scalaz.Scalaz._
import scalaz._

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

case class SketchComponentIntro( component: AvatarDefinition ) extends RefutationSketch {
  def immediateSubProofs = Seq()
  def conclusion = component.clause.map( _.asInstanceOf[FOLAtom] )
}
case class SketchComponentElim( subProof: RefutationSketch, component: AvatarDefinition ) extends RefutationSketch {
  def immediateSubProofs = Seq( subProof )
  val conclusion = subProof.conclusion diff component.clause
}

case class SketchSplitCombine( splitCases: Seq[RefutationSketch] ) extends RefutationSketch {
  for ( p <- splitCases ) require( p.conclusion.isEmpty, p )

  override def immediateSubProofs = splitCases
  override def conclusion = FOLClause()

  override def productArity = splitCases.size
  override def productElement( n: Int ) = splitCases( n )
}

case class UnprovableSketchInference( inference: RefutationSketch ) {
  override def toString = s"\nCannot prove\n${inference.conclusion}\n\nfrom\n\n${inference.immediateSubProofs.map( _.conclusion ).mkString( "\n\n" )}\n"
}

object RefutationSketchToResolution {
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
  def apply( sketch: RefutationSketch, prover: ResolutionProver = NonSplittingEscargot ): ValidationNel[UnprovableSketchInference, ResolutionProof] = {
    type ErrorOr[X] = ValidationNel[UnprovableSketchInference, X]
    val memo = mutable.Map[RefutationSketch, ErrorOr[ResolutionProof]]()

    def findDerivation( a: FOLClause, bs: List[ResolutionProof] ): Option[ResolutionProof] = {
      for ( b <- bs; s <- clauseSubsumption( b.conclusion, a ) ) return Some( Subst.ifNecessary( b, s ) )
      findDerivationViaResolution( a, bs.map( _.conclusion.asInstanceOf[HOLClause] ).toSet, prover ).
        map( mapInputClauses( _ )( bs.map { p => p.conclusion -> p }.toMap ) )
    }
    def solve( s: RefutationSketch ): ErrorOr[ResolutionProof] = memo.getOrElseUpdate( s, s match {
      case SketchAxiom( axiom ) => Success( Input( axiom ) )
      case s @ SketchInference( conclusion, from ) =>
        import Validation.FlatMap._
        for {
          solvedFrom <- Applicative[ErrorOr].traverse( from.toList )( solve )
          deriv <- findDerivation( s.conclusion, solvedFrom ).map { _.success }.
            getOrElse { UnprovableSketchInference( s ).failureNel }
        } yield deriv
      case SketchSplitCombine( cases ) =>
        import Validation.FlatMap._
        Applicative[ErrorOr].traverse( cases.toList )( solve ).flatMap { solvedCases =>
          solvedCases.find( p => p.conclusion.isEmpty && p.assertions.isEmpty ).
            orElse( Sat4j.getResolutionProof( solvedCases.map( AvatarContradiction( _ ) ) ) ).
            orElse( NonSplittingEscargot.getResolutionProof( solvedCases.map( AvatarContradiction( _ ) ) ) ).
            map( _.success ).getOrElse( UnprovableSketchInference( s ).failureNel )
        }
      case SketchComponentElim( from, comp ) =>
        for ( solvedFrom <- solve( from ) )
          yield AvatarSplit( solvedFrom, comp )
      case SketchComponentIntro( comp ) =>
        AvatarComponent( comp ).success
    } )
    solve( sketch ) map { simplifyResolutionProof( _ ) }
  }

}
