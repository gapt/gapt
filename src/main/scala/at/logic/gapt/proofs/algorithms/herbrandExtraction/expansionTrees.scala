package at.logic.gapt.proofs.algorithms.herbrandExtraction

import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr._
import at.logic.gapt.language.hol._
import at.logic.gapt.proofs.expansionTrees.{ ETWeakQuantifier, ETStrongQuantifier, ETAnd, ETOr, ETImp, ETNeg, ETAtom, ETMerge, ExpansionSequent, ExpansionTreeWithMerges, merge => mergeTree }
import at.logic.gapt.proofs.occurrences._

object extractExpansionSequent extends extractExpansionSequent
class extractExpansionSequent {

  def apply( proof: LKProof, verbose: Boolean ): ExpansionSequent = {
    val map = extract( proof, verbose )
    val clean_ant = proof.root.antecedent.filter( f => map( f ) != ETAtom( Top() ) )
    val clean_suc = proof.root.succedent.filter( f => map( f ) != ETAtom( Bottom() ) )
    mergeTree( ( clean_ant.map( fo => map( fo ) ), clean_suc.map( fo => map( fo ) ) ) )
  }

  private def extract( proof: LKProof, verbose: Boolean ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = proof match {
    case Axiom( r ) =>
      handleAxiom( r, verbose )
    case UnaryLKProof( _, up, r, _, p ) =>
      val map = extract( up, verbose )
      handleUnary( r, p, map, proof )

    case CutRule( up1, up2, r, _, _ ) => getMapOfContext( ( r.antecedent ++ r.succedent ).toSet, extract( up1, verbose ) ++ extract( up2, verbose ) )
    case BinaryLKProof( _, up1, up2, r, a1, a2, Some( p ) ) =>
      val map = extract( up1, verbose ) ++ extract( up2, verbose )
      handleBinary( r, map, proof, a1, a2, p )

    case _ => throw new IllegalArgumentException( "unsupported proof rule: " + proof )
  }

  def handleAxiom( r: Sequent, verbose: Boolean ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = {
    // guess the axiom: must be an atom and appear left as well as right
    // can't use set intersection, but lists are small enough to do it manually
    val axiomCandidates = r.antecedent.filter( elem => r.succedent.exists( elem2 => elem syntaxEquals elem2 ) ).filter( o => isAtom( o.formula ) || o.formula == Bottom() || o.formula == Top() )

    if ( axiomCandidates.size > 1 && verbose ) {
      println( "Warning: Multiple candidates for axiom formula in expansion tree extraction, choosing first one of: " + axiomCandidates )
    }

    if ( axiomCandidates.isEmpty ) {
      if ( allAtoms( r.antecedent ) && allAtoms( r.succedent ) ) {
        if ( !( ( r.antecedent.isEmpty ) && ( r.succedent.size == 1 ) && ( isReflexivity( r.succedent( 0 ).formula ) ) ) && verbose ) {
          //only print the warning for non reflexivity atoms
          println( "Warning: No candidates for axiom formula in expansion tree extraction, treating as atom trees since axiom only contains atoms: " + r )
        }
        Map( r.antecedent.map( fo => ( fo, ETAtom( fo.formula ) ) ) ++
          r.succedent.map( fo => ( fo, ETAtom( fo.formula ) ) ): _* )
      } else {
        throw new IllegalArgumentException( "Error: Axiom sequent in expansion tree extraction contains no atom A on left and right side and contains non-atomic formulas: " + r )
      }

      // this behaviour is convenient for development, as it allows to work reasonably with invalid axioms
      Map( r.antecedent.map( fo => ( fo, ETAtom( fo.formula ) ) ) ++
        r.succedent.map( fo => ( fo, ETAtom( fo.formula ) ) ): _* )
    } else {
      val axiomFormula = axiomCandidates( 0 )

      Map( r.antecedent.map( fo => ( fo, ETAtom( if ( fo syntaxEquals axiomFormula ) fo.formula else Top() ) ) ) ++
        r.succedent.map( fo => ( fo, ETAtom( if ( fo syntaxEquals axiomFormula ) fo.formula else Bottom() ) ) ): _* )
    }
  }

  //occurs in handleAxiom
  private def allAtoms( l: Seq[FormulaOccurrence] ) = l.forall( o => isAtom( o.formula ) || o.formula == Top() || o.formula == Bottom() )
  private def isReflexivity( f: Formula ) = f match { case Eq( s, t ) if s == t => true; case _ => false }

  def handleUnary( r: Sequent, p: FormulaOccurrence, map: Map[FormulaOccurrence, ExpansionTreeWithMerges], proof: LKProof ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = {
    getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map ) + Tuple2( p, proof match {
      case WeakeningRightRule( _, _, _ )           => ETAtom( Bottom() )
      case WeakeningLeftRule( _, _, _ )            => ETAtom( Top() )
      case ForallLeftRule( _, _, a, _, t )         => ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) )
      case ExistsRightRule( _, _, a, _, t )        => ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) )
      case ForallRightRule( _, _, a, _, v )        => ETStrongQuantifier( p.formula, v, map( a ) )
      case ExistsLeftRule( _, _, a, _, v )         => ETStrongQuantifier( p.formula, v, map( a ) )
      case ContractionLeftRule( _, _, a1, a2, _ )  => ETMerge( map( a1 ), map( a2 ) )
      case ContractionRightRule( _, _, a1, a2, _ ) => ETMerge( map( a1 ), map( a2 ) )
      case AndLeft1Rule( _, _, a, _ ) =>
        val And( _, f2 ) = p.formula
        ETAnd( map( a ), ETAtom( Top() ) )
      case AndLeft2Rule( _, _, a, _ ) =>
        val And( f1, _ ) = p.formula
        ETAnd( ETAtom( Top() ), map( a ) )
      case OrRight1Rule( _, _, a, _ ) =>
        val Or( _, f2 ) = p.formula
        ETOr( map( a ), ETAtom( Bottom() ) )
      case OrRight2Rule( _, _, a, _ ) =>
        val Or( f1, _ ) = p.formula
        ETOr( ETAtom( Bottom() ), map( a ) )
      case ImpRightRule( _, _, a1, a2, _ ) =>
        ETImp( map( a1 ), map( a2 ) )
      case NegLeftRule( _, _, a, _ )         => ETNeg( map( a ) )
      case NegRightRule( _, _, a, _ )        => ETNeg( map( a ) )
      case DefinitionLeftRule( _, _, a, _ )  => map( a )
      case DefinitionRightRule( _, _, a, _ ) => map( a )
    } )
  }

  def handleBinary( r: Sequent, map: Map[FormulaOccurrence, ExpansionTreeWithMerges], proof: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, p: FormulaOccurrence ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = {
    getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map ) + Tuple2( p, proof match {
      case ImpLeftRule( _, _, _, _, _, _ )           => ETImp( map( a1 ), map( a2 ) )
      case OrLeftRule( _, _, _, _, _, _ )            => ETOr( map( a1 ), map( a2 ) )
      case AndRightRule( _, _, _, _, _, _ )          => ETAnd( map( a1 ), map( a2 ) )
      case EquationLeft1Rule( _, _, _, _, _, _, _ )  => map( a2 )
      case EquationLeft2Rule( _, _, _, _, _, _, _ )  => map( a2 )
      case EquationRight1Rule( _, _, _, _, _, _, _ ) => map( a2 )
      case EquationRight2Rule( _, _, _, _, _, _, _ ) => map( a2 )
    } )
  }

  // the set of formula occurrences given to method must not contain any principal formula
  private[herbrandExtraction] def getMapOfContext( s: Set[FormulaOccurrence], map: Map[FormulaOccurrence, ExpansionTreeWithMerges] ): Map[FormulaOccurrence, ExpansionTreeWithMerges] =
    Map( s.toList.map( fo => ( fo, {
      require( fo.parents.size == 1 )
      map( fo.parents.head )
    } ) ): _* )

}
