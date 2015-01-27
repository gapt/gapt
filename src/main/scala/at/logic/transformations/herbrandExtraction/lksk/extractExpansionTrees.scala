package at.logic.transformations.herbrandExtraction.lksk

import at.logic.transformations.herbrandExtraction.extractExpansionSequent
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.expansionTrees.{merge => mergeTree, Atom => AtomTree, _}
import at.logic.calculi.occurrences.FormulaOccurrence

import at.logic.calculi.lksk._
import scala.Tuple2
import at.logic.language.hol.{TopC, BottomC}
import at.logic.calculi.lk.{BinaryLKProof, CutRule, UnaryLKProof}

/**
 * Extends expansion tree extraction to lksk.
 */
object extractLKSKExpansionSequent extends extractLKSKExpansionSequent;
class extractLKSKExpansionSequent  extends extractExpansionSequent {
  override def apply(proof: LKProof, verbose: Boolean): ExpansionSequent = {
    val map = extract(proof, verbose)
    mergeTree( (proof.root.antecedent.map(fo => map(fo)), proof.root.succedent.map(fo => map(fo))) )
  }

  def extract(proof: LKProof, verbose: Boolean): Map[FormulaOccurrence,ExpansionTreeWithMerges] = proof match {
    case Axiom(r) =>
      handleAxiom(r, verbose)

    case WeakeningRightRule(parent, r, p) =>
      val map = extract(parent, verbose)
      val contextmap = getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map)
      contextmap + ((p, AtomTree(BottomC)))
    case WeakeningLeftRule(parent, r, p) =>
      val map = extract(parent, verbose)
      val contextmap = getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map)
      contextmap + ((p, AtomTree(TopC)))
    case ForallSkLeftRule(parent, r, a, p, t) =>
      val map = extract(parent, verbose)
      val contextmap = getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map)
      contextmap + ((p, WeakQuantifier(p.formula, List(Tuple2(map(a), t)))))
    case ExistsSkRightRule(parent, r, a, p, t) =>
      val map = extract(parent, verbose)
      val contextmap = getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map)
      contextmap + ((p, WeakQuantifier(p.formula, List(Tuple2(map(a), t)))))
    case ForallSkRightRule(parent, r, a, p, skt) =>
      val map = extract(parent, verbose)
      val contextmap = getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map)
      contextmap + ((p, SkolemQuantifier(p.formula,  skt, map(a) )))
    case ExistsSkLeftRule(parent, r, a, p, skt) =>
      val map = extract(parent, verbose)
      val contextmap = getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map)
      contextmap + ((p, SkolemQuantifier(p.formula,  skt, map(a) )))


    case UnaryLKProof(_,up,r,_,p) =>
      val map = extract(up, verbose)
      handleUnary(r, p, map, proof)

    case CutRule(up1,up2,r,_,_) =>
      getMapOfContext((r.antecedent ++ r.succedent).toSet, extract(up1, verbose) ++ extract(up2, verbose))

    case BinaryLKProof(_,up1,up2,r,a1,a2,Some(p)) =>
      val map = extract(up1, verbose) ++ extract(up2, verbose)
      handleBinary(r, map, proof, a1, a2, p)

  }


}
