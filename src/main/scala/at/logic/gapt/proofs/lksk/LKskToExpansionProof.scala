package at.logic.gapt.proofs.lksk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkOld.{ BinaryLKProof, CutRule, UnaryLKProof, LKToExpansionProof }
import at.logic.gapt.proofs.lkOld.base.LKProof
import at.logic.gapt.proofs.expansionTrees.{ merge => mergeTree, _ }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * Extends expansion tree extraction to lksk.
 */
object LKskToExpansionProof extends LKskToExpansionProof;
class LKskToExpansionProof extends LKToExpansionProof {
  override def apply( proof: LKProof ): ExpansionSequent = {
    val map = extract( proof )
    mergeTree( ( proof.root.antecedent.map( fo => map( fo ) ), proof.root.succedent.map( fo => map( fo ) ) ) )
  }

  def extract( proof: LKProof ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = proof match {
    case Axiom( r ) =>
      handleAxiom( r )

    case WeakeningRightRule( parent, r, p ) =>
      val map = extract( parent )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETWeakening( p.formula ) ) )
    case WeakeningLeftRule( parent, r, p ) =>
      val map = extract( parent )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETWeakening( p.formula ) ) )
    case ForallSkLeftRule( parent, r, a, p, t ) =>
      val map = extract( parent )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) ) ) )
    case ExistsSkRightRule( parent, r, a, p, t ) =>
      val map = extract( parent )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) ) ) )
    case ForallSkRightRule( parent, r, a, p, skt ) =>
      val map = extract( parent )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETSkolemQuantifier( p.formula, skt, map( a ) ) ) )
    case ExistsSkLeftRule( parent, r, a, p, skt ) =>
      val map = extract( parent )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETSkolemQuantifier( p.formula, skt, map( a ) ) ) )

    case UnaryLKProof( _, up, r, _, p ) =>
      val map = extract( up )
      handleUnary( r, p, map, proof )

    case CutRule( up1, up2, r, _, _ ) =>
      getMapOfContext( ( r.antecedent ++ r.succedent ).toSet, extract( up1 ) ++ extract( up2 ) )

    case BinaryLKProof( _, up1, up2, r, a1, a2, Some( p ) ) =>
      val map = extract( up1 ) ++ extract( up2 )
      handleBinary( r, map, proof, a1, a2, p )

  }
}
