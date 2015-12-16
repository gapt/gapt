package at.logic.gapt.proofs.lkOld

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.expansionTrees.{ merge => mergeTree, _ }
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.utils.logging.Logger

object LKToExpansionProof extends LKToExpansionProof
class LKToExpansionProof extends Logger {

  def apply( proof: LKProof ): ExpansionSequent = {
    val map = extract( proof )
    mergeTree( ( proof.root.antecedent.map( fo => map( fo ) ), proof.root.succedent.map( fo => map( fo ) ) ) )
  }

  private def extract( proof: LKProof ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = proof match {
    case Axiom( r ) =>
      handleAxiom( r )
    case UnaryLKProof( _, up, r, _, p ) =>
      val map = extract( up )
      handleUnary( r, p, map, proof )

    case CutRule( up1, up2, r, _, _ ) => getMapOfContext( ( r.antecedent ++ r.succedent ).toSet, extract( up1 ) ++ extract( up2 ) )
    case BinaryLKProof( _, up1, up2, r, a1, a2, Some( p ) ) =>
      val map = extract( up1 ) ++ extract( up2 )
      handleBinary( r, map, proof, a1, a2, p )

    case _ => throw new IllegalArgumentException( "unsupported proof rule: " + proof )
  }

  protected def handleAxiom( r: OccSequent ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = {
    // guess the axiom: must be an atom and appear left as well as right
    // can't use set intersection, but lists are small enough to do it manually
    val axiomCandidates = r.antecedent.filter( elem => r.succedent.exists( elem2 => elem syntaxEquals elem2 ) ).filter( o => isExtendedAtom( o.formula ) )

    if ( axiomCandidates.size > 1 ) {
      debug( "Warning: Multiple candidates for axiom formula in expansion tree extraction, choosing first one of: " + axiomCandidates )
    }

    if ( axiomCandidates.isEmpty ) {
      if ( allExtendedAtoms( r.antecedent ) && allExtendedAtoms( r.succedent ) ) {
        if ( !( ( r.antecedent.isEmpty ) && ( r.succedent.size == 1 ) && ( isReflexivity( r.succedent( 0 ).formula ) ) ) ) {
          //only print the warning for non reflexivity atoms
          debug( "Warning: No candidates for axiom formula in expansion tree extraction, treating as atom trees since axiom only contains atoms: " + r )
        }
        Map( r.antecedent.map( fo => ( fo, ETInitialNode( fo.formula ) ) ) ++
          r.succedent.map( fo => ( fo, ETInitialNode( fo.formula ) ) ): _* )
      } else {
        throw new IllegalArgumentException( "Error: Axiom sequent in expansion tree extraction contains no atom A on left and right side and contains non-atomic formulas: " + r )
      }

      // this behaviour is convenient for development, as it allows to work reasonably with invalid axioms
      Map( r.antecedent.map( fo => ( fo, ETInitialNode( fo.formula ) ) ) ++
        r.succedent.map( fo => ( fo, ETInitialNode( fo.formula ) ) ): _* )
    } else {
      val axiomFormula = axiomCandidates( 0 )

      Map( r.antecedent.map( fo => ( fo, if ( fo syntaxEquals axiomFormula ) ETInitialNode( fo.formula ) else ETWeakening( fo.formula ) ) ) ++
        r.succedent.map( fo => ( fo, if ( fo syntaxEquals axiomFormula ) ETInitialNode( fo.formula ) else ETWeakening( fo.formula ) ) ): _* )
    }
  }

  //occurs in handleAxiom
  private def allExtendedAtoms( l: Seq[FormulaOccurrence] ) = l.forall( o => isExtendedAtom( o.formula ) )

  protected def handleUnary( r: OccSequent, p: FormulaOccurrence, map: Map[FormulaOccurrence, ExpansionTreeWithMerges], proof: LKProof ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = {
    getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map ) + Tuple2( p, proof match {
      case WeakeningRightRule( _, _, _ )           => ETWeakening( p.formula )
      case WeakeningLeftRule( _, _, _ )            => ETWeakening( p.formula )
      case ForallLeftRule( _, _, a, _, t )         => ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) )
      case ExistsRightRule( _, _, a, _, t )        => ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) )
      case ForallRightRule( _, _, a, _, v )        => ETStrongQuantifier( p.formula, v, map( a ) )
      case ExistsLeftRule( _, _, a, _, v )         => ETStrongQuantifier( p.formula, v, map( a ) )
      case ContractionLeftRule( _, _, a1, a2, _ )  => ETMerge( map( a1 ), map( a2 ) )
      case ContractionRightRule( _, _, a1, a2, _ ) => ETMerge( map( a1 ), map( a2 ) )
      case AndLeft1Rule( _, _, a, _ ) =>
        val And( _, f2 ) = p.formula
        ETAnd( map( a ), ETWeakening( f2 ) )
      case AndLeft2Rule( _, _, a, _ ) =>
        val And( f1, _ ) = p.formula
        ETAnd( ETWeakening( f1 ), map( a ) )
      case OrRight1Rule( _, _, a, _ ) =>
        val Or( _, f2 ) = p.formula
        ETOr( map( a ), ETWeakening( f2 ) )
      case OrRight2Rule( _, _, a, _ ) =>
        val Or( f1, _ ) = p.formula
        ETOr( ETWeakening( f1 ), map( a ) )
      case ImpRightRule( _, _, a1, a2, _ ) =>
        ETImp( map( a1 ), map( a2 ) )
      case NegLeftRule( _, _, a, _ )         => ETNeg( map( a ) )
      case NegRightRule( _, _, a, _ )        => ETNeg( map( a ) )
      case DefinitionLeftRule( _, _, a, _ )  => map( a )
      case DefinitionRightRule( _, _, a, _ ) => map( a )
    } )
  }

  protected def handleBinary( r: OccSequent, map: Map[FormulaOccurrence, ExpansionTreeWithMerges], proof: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, p: FormulaOccurrence ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = {
    getMapOfContext( r.elements.toSet - p, map ) + Tuple2( p, proof match {
      case ImpLeftRule( _, _, _, _, _, _ )  => ETImp( map( a1 ), map( a2 ) )
      case OrLeftRule( _, _, _, _, _, _ )   => ETOr( map( a1 ), map( a2 ) )
      case AndRightRule( _, _, _, _, _, _ ) => ETAnd( map( a1 ), map( a2 ) )
      case EquationLeft1Rule( _, _, _, _, _, pos, _ ) =>
        val repTerm = p( pos.head )
        replaceAtHOLPosition( map( a2 ), pos.head, repTerm )
      case EquationLeft2Rule( _, _, _, _, _, pos, _ ) =>
        val repTerm = p( pos.head )
        replaceAtHOLPosition( map( a2 ), pos.head, repTerm )
      case EquationRight1Rule( _, _, _, _, _, pos, _ ) =>
        val repTerm = p( pos.head )
        replaceAtHOLPosition( map( a2 ), pos.head, repTerm )
      case EquationRight2Rule( _, _, _, _, _, pos, _ ) =>
        val repTerm = p( pos.head )
        replaceAtHOLPosition( map( a2 ), pos.head, repTerm )
    } )
  }

  // the set of formula occurrences given to method must not contain any principal formula
  protected def getMapOfContext( s: Set[FormulaOccurrence], map: Map[FormulaOccurrence, ExpansionTreeWithMerges] ): Map[FormulaOccurrence, ExpansionTreeWithMerges] =
    Map( s.toList.map( fo => ( fo, {
      require( fo.parents.size == 1 )
      map( fo.parents.head )
    } ) ): _* )

}
