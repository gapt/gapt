package at.logic.gapt.prooftool

import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.lkOld.base.{ OccSequent, BinaryLKProof, UnaryLKProof, NullaryLKProof }
import at.logic.gapt.proofs.proofs.{ BinaryProof, UnaryProof, Proof, NullaryProof, TreeProof }
import at.logic.gapt.formats.latex.LatexUIRenderer.{ formulaToLatexString, labelledFormulaToLatexString, formulaOccurrenceToLatexString }

object Search {

  def inTreeProof( str: String, proof: TreeProof[_] ): Set[FormulaOccurrence] = proof match {
    case p: NullaryLKProof =>
      ( p.root.antecedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ++
        p.root.succedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ).toSet
    case p: UnaryLKProof =>
      inTreeProof( str, p.uProof.asInstanceOf[TreeProof[_]] ) ++
        ( p.root.antecedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ++
          p.root.succedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ).toSet
    case p: BinaryLKProof =>
      inTreeProof( str, p.uProof1.asInstanceOf[TreeProof[_]] ) ++
        inTreeProof( str, p.uProof2.asInstanceOf[TreeProof[_]] ) ++
        ( p.root.antecedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ++
          p.root.succedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ).toSet
    case _ => throw new Exception( "Cannot search in this object!" )
  }

  def inResolutionProof( str: String, tree: Proof[_] ): Set[FormulaOccurrence] = tree match {
    case p: NullaryProof[_] => p.root match {
      case s: OccSequent =>
        ( s.antecedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ++
          s.succedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ).toSet
    }
    case p: UnaryProof[_] => p.root match {
      case s: OccSequent =>
        inResolutionProof( str, p.uProof ) ++
          ( s.antecedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ++
            s.succedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ).toSet
    }
    case p: BinaryProof[_] => p.root match {
      case s: OccSequent =>
        inResolutionProof( str, p.uProof1 ) ++ inResolutionProof( str, p.uProof2 ) ++
          ( s.antecedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ++
            s.succedent.filter( fo => formulaToLatexString( fo.formula ).contains( str ) ) ).toSet
    }
    case _ => throw new Exception( "Cannot search in this object!" )
  }
}
