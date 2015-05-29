package at.logic.gapt.proofs.algorithms.herbrandExtraction.lksk

import at.logic.gapt.proofs.algorithms.herbrandExtraction.extractExpansionSequent
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.proofs.expansionTrees.{ merge => mergeTree, ETAtom => AtomTree, _ }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

import at.logic.gapt.proofs.lksk._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.{ BinaryLKProof, CutRule, UnaryLKProof }

/**
 * Extends expansion tree extraction to lksk.
 */
object extractLKSKExpansionSequent extends extractLKSKExpansionSequent;
class extractLKSKExpansionSequent extends extractExpansionSequent {
  override def apply( proof: LKProof, verbose: Boolean ): ExpansionSequent = {
    val map = extract( proof, verbose )
    mergeTree( ( proof.root.antecedent.map( fo => map( fo ) ), proof.root.succedent.map( fo => map( fo ) ) ) )
  }

  def extract( proof: LKProof, verbose: Boolean ): Map[FormulaOccurrence, ExpansionTreeWithMerges] = proof match {
    case Axiom( r ) =>
      handleAxiom( r, verbose )

    case WeakeningRightRule( parent, r, p ) =>
      val map = extract( parent, verbose )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, AtomTree( Bottom() ) ) )
    case WeakeningLeftRule( parent, r, p ) =>
      val map = extract( parent, verbose )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, AtomTree( Top() ) ) )
    case ForallSkLeftRule( parent, r, a, p, t ) =>
      val map = extract( parent, verbose )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) ) ) )
    case ExistsSkRightRule( parent, r, a, p, t ) =>
      val map = extract( parent, verbose )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETWeakQuantifier( p.formula, List( Tuple2( map( a ), t ) ) ) ) )
    case ForallSkRightRule( parent, r, a, p, skt ) =>
      val map = extract( parent, verbose )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETSkolemQuantifier( p.formula, skt, map( a ) ) ) )
    case ExistsSkLeftRule( parent, r, a, p, skt ) =>
      val map = extract( parent, verbose )
      val contextmap = getMapOfContext( ( r.antecedent ++ r.succedent ).toSet - p, map )
      contextmap + ( ( p, ETSkolemQuantifier( p.formula, skt, map( a ) ) ) )

    case UnaryLKProof( _, up, r, _, p ) =>
      val map = extract( up, verbose )
      handleUnary( r, p, map, proof )

    case CutRule( up1, up2, r, _, _ ) =>
      getMapOfContext( ( r.antecedent ++ r.succedent ).toSet, extract( up1, verbose ) ++ extract( up2, verbose ) )

    case BinaryLKProof( _, up1, up2, r, a1, a2, Some( p ) ) =>
      val map = extract( up1, verbose ) ++ extract( up2, verbose )
      handleBinary( r, map, proof, a1, a2, p )

  }

}
