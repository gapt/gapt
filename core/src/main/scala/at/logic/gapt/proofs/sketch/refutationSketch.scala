package at.logic.gapt.proofs.sketch

import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.expr.{ FOLAtom, HOLAtom, HOLFormula, constants, freeVariables, rename }
import at.logic.gapt.proofs.{ FOLClause, HOLClause, OccConnector, RichFOLSequent, Sequent, SequentProof }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.{ findDerivationViaResolution, mapInputClauses }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.escargot.{ Escargot, NonSplittingEscargot }
import at.logic.gapt.provers.sat.Sat4j

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
    splittingClause: RefutationSketch, part1: FOLClause
) extends RefutationSketch {
  require( part1 isSubMultisetOf splittingClause.conclusion )
  val part2 = splittingClause.conclusion diff part1

  val definition1 = univclosure( part1.toDisjunction )
  val definition2 = univclosure( part2.toDisjunction )

  val addAxioms1 = Seq( part1 )

  val groundNegPart1 = part1.filter( freeVariables( _ ).isEmpty ).map( FOLClause() :+ _, _ +: FOLClause() ).elements
  val addAxioms2 = Seq( part2 ) ++ groundNegPart1

  override def immediateSubProofs = Seq( splittingClause )
  override def conclusion = FOLClause()
}
case class SketchSplit1( split: SketchSplit ) extends RefutationSketch {
  def immediateSubProofs = Seq( split )
  def conclusion = split.addAxioms1.head
}
case class SketchSplit2( split: SketchSplit, i: Int ) extends RefutationSketch {
  def immediateSubProofs = Seq( split )
  def conclusion = split.addAxioms2( i )
}

case class SketchComponentIntro( component: AvatarComponent ) extends RefutationSketch {
  def immediateSubProofs = Seq()
  def conclusion = component.clause.map( _.asInstanceOf[FOLAtom] )
}
case class SketchComponentElim( subProof: RefutationSketch, component: AvatarComponent ) extends RefutationSketch {
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

case class UnprovableSketchInference( inference: RefutationSketch )

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
  def apply( sketch: RefutationSketch, prover: ResolutionProver = NonSplittingEscargot ): ValidationNel[UnprovableSketchInference, ResolutionProof] = {
    val nameGen = rename.awayFrom( constants( sketch.subProofs.view.flatMap( _.conclusion.elements ) ) )
    val splitConsts = mutable.Map[SketchSplit, ( FOLAtom, FOLAtom )]()
    def mkSplitConst( split: SketchSplit ) =
      splitConsts.getOrElseUpdate( split, ( FOLAtom( nameGen.freshWithIndex( "_split1" ) ), FOLAtom( nameGen.freshWithIndex( "_split2" ) ) ) )

    type ErrorOr[X] = ValidationNel[UnprovableSketchInference, X]
    val memo = mutable.Map[RefutationSketch, ErrorOr[ResolutionProof]]()
    def solve( s: RefutationSketch ): ErrorOr[ResolutionProof] = memo.getOrElseUpdate( s, s match {
      case SketchAxiom( axiom ) => Success( Input( axiom ) )
      case SketchSplit1( split ) =>
        AvatarComponentIntro( AvatarNonGroundComp( mkSplitConst( split )._1, split.definition1 ) ).success
      case SketchSplit2( split, 0 ) =>
        AvatarComponentIntro( AvatarNonGroundComp( mkSplitConst( split )._2, split.definition2 ) ).success
      case s @ SketchSplit2( split, i ) if i > 0 =>
        val AvatarNonGroundComp.DefinitionFormula( vs, clause ) = split.definition1
        val j =
          s.conclusion match {
            case Sequent( Seq(), Seq( a ) ) => clause.indexOfInAnt( a )
            case Sequent( Seq( a ), Seq() ) => clause.indexOfInSuc( a )
          }
        AvatarComponentIntro( AvatarNegNonGroundComp( mkSplitConst( split )._1, split.definition1, vs, j ) ).success
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
        val comp1 = AvatarNonGroundComp( mkSplitConst( s )._1, s.definition1 )
        val comp2 = AvatarNonGroundComp( mkSplitConst( s )._2, s.definition2 )
        for ( splittingClause <- solve( s.splittingClause ) )
          yield AvatarSplit( splittingClause, Seq( comp1, comp2 ) )
      case SketchSplitCombine( cases ) =>
        import Validation.FlatMap._
        for {
          solvedCases <- Applicative[ErrorOr].traverse( cases.toList )( solve )
          refutation <- Sat4j.getRobinsonProof( solvedCases.map( AvatarAbsurd( _ ) ) ).
            map { _.success }.
            getOrElse { UnprovableSketchInference( s ).failureNel }
        } yield refutation
      case SketchComponentElim( from, comp ) =>
        for ( solvedFrom <- solve( from ) )
          yield AvatarComponentElim( solvedFrom, comp )
      case SketchComponentIntro( comp ) =>
        AvatarComponentIntro( comp ).success
    } )
    solve( sketch ) map { simplifyResolutionProof( _ ) }
  }
}
