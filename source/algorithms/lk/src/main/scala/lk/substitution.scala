package at.logic.algorithms.lk

import scala.collection.mutable.{Map, HashMap}

import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol.substitutions.Substitution
import at.logic.language.hol.propositions._

// TODO: also apply substitution to labels in LKsk!
// perhaps make a new class for LKsk, which deals only with LKsk specific parts?

object applySubstitution {
  def handleRule( proof: LKProof, new_parents: List[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
                  subst: Substitution ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = proof match {
    case Axiom(so) => {
      val ant_occs = so.antecedent.toList
      val succ_occs = so.succedent.toList
      val a = Axiom(Sequent(ant_occs.map( fo => subst(fo.formula) ), succ_occs.map( fo => subst(fo.formula) ) ) )
      val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
      a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
      a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
      (a._1, map)
    }
    case WeakeningLeftRule(p, s, m) => {
      val new_parent = new_parents.first
      val new_proof = WeakeningLeftRule( new_parent._1, subst(m.formula) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.first ) )
    }
    case WeakeningRightRule(p, s, m) => {
      val new_parent = new_parents.first
      val new_proof = WeakeningRightRule( new_parent._1, subst(m.formula) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.first ) )
    }
    case ContractionLeftRule(p, s, a1, a2, m) => {
      val new_parent = new_parents.first
      val new_proof = ContractionLeftRule( new_parent._1, new_parent._2( a1 ), new_parent._2( a2 ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case ContractionRightRule(p, s, a1, a2, m) => {
      val new_parent = new_parents.first
      val new_proof = ContractionRightRule( new_parent._1, new_parent._2( a1 ), new_parent._2( a2 ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case CutRule(p1, p2, s, a1, a2) => {
      val new_p1 = new_parents.first
      val new_p2 = new_parents.last
      val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
      ( new_proof, computeMap( 
        p1.root.antecedent ++ (p1.root.succedent - a1) ++ (p2.root.antecedent - a2) ++ p2.root.succedent,
        proof, new_proof, new_p1._2 ++ new_p2._2 ) )
    }
    case AndRightRule(p1, p2, s, a1, a2, m) => {
      val new_p1 = new_parents.first
      val new_p2 = new_parents.last
      val new_proof = AndRightRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
      ( new_proof, computeMap( p1.root.antecedent ++ p1.root.succedent ++ p2.root.antecedent ++ p2.root.succedent,
        proof, new_proof, new_p1._2 ++ new_p2._2 ) )
    }
    case AndLeft1Rule(p, s, a, m) => {
      val f = m.formula match { case And(_, f) => f }
      val new_parent = new_parents.first
      val new_proof = AndLeft1Rule( new_parent._1, new_parent._2( a ), subst( f ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case AndLeft2Rule(p, s, a, m) => {
      val f = m.formula match { case And(f, _) => f }
      val new_parent = new_parents.first
      val new_proof = AndLeft2Rule( new_parent._1, subst( f ), new_parent._2( a ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case OrLeftRule(p1, p2, s, a1, a2, m) => {
      val new_p1 = new_parents.first
      val new_p2 = new_parents.last
      val new_proof = OrLeftRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
      ( new_proof, computeMap( p1.root.succedent ++ p1.root.succedent ++ p2.root.antecedent ++ p2.root.succedent,
        proof, new_proof, new_p1._2 ++ new_p2._2 ) )
    }
    case OrRight1Rule(p, s, a, m) => {
      val f = m.formula match { case Or(_, f) => f }
      val new_parent = new_parents.first
      val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), subst( f ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case OrRight2Rule(p, s, a, m) => {
      val f = m.formula match { case Or(f, _) => f }
      val new_parent = new_parents.first
      val new_proof = OrRight2Rule( new_parent._1, subst( f ), new_parent._2( a ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case ImpLeftRule(p1, p2, s, a1, a2, m) => {
      val new_p1 = new_parents.first
      val new_p2 = new_parents.last
      val new_proof = ImpLeftRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
      ( new_proof, computeMap( p1.root.succedent ++ p1.root.succedent ++ p2.root.antecedent ++ p2.root.succedent,
        proof, new_proof, new_p1._2 ++ new_p2._2 ) )
    }
    case ImpRightRule(p, s, a1, a2, m) => {
      val new_parent = new_parents.first
      val new_proof = ImpRightRule( new_parent._1,
                                    new_parent._2( a1 ),
                                    new_parent._2( a2 ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case NegLeftRule(p, s, a, m) => {
      val new_parent = new_parents.first
      val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
    case NegRightRule(p, s, a, m) => {
      val new_parent = new_parents.first
      val new_proof = NegRightRule( new_parent._1, new_parent._2( a ) )
      ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }

}

def apply( proof: LKProof, subst: Substitution ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) =
  proof match {
    case Axiom(_) => handleRule( proof, Nil, subst )
    case UnaryLKProof(_, p, _, _, _) => handleRule( proof, apply( p, subst )::Nil, subst )
    case BinaryLKProof(_, p1, p2, _, _, _, _) =>
      handleRule( proof, apply( p1, subst )::apply( p2, subst )::Nil, subst )
  }

  // TODO: a very similar method is used in LKtoLKskc, refactor!?
  def computeMap( occs: Set[FormulaOccurrence], old_proof: LKProof, 
                  new_proof: LKProof, old_map : Map[FormulaOccurrence, FormulaOccurrence]) =
  {
    val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get, 
      new_proof.getDescendantInLowerSequent( old_map(fo) ).get ) )
    map
  }
}
