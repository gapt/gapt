package at.logic.algorithms.lk

import scala.collection.immutable.{Set, EmptySet}
import scala.collection.mutable.{Map, HashMap}

import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lksk.lkskExtractors.{UnaryLKskProof}
import at.logic.language.hol.propositions._

// TODO: we use the toSet method from axiom here to convert a list to a set,
// perhaps refactor this method out of axiom - it seems useful in general
object getCutAncestors {
  def apply( p: LKProof )
    : Set[FormulaOccurrence] = p match {
      case CutRule(p1, p2, _, a1, a2) => getCutAncestors( p1 ) ++ getCutAncestors( p2 ) ++ 
                                         Axiom.toSet( getAncestors( a1 ) ) ++ Axiom.toSet( getAncestors( a2 ) )
      case UnaryLKProof(_,p,_,_,_) => getCutAncestors( p )
      case BinaryLKProof(_, p1, p2, _, _, _, _) => getCutAncestors( p1 ) ++ getCutAncestors( p2 )
      case Axiom(so) => Set[FormulaOccurrence]()
      // support LKsk
      case UnaryLKskProof(_,p,_,_,_) => getCutAncestors( p )
    }
  def getAncestors( o: FormulaOccurrence ) : List[FormulaOccurrence] =
    o.ancestors.flatMap( a => getAncestors( a ) ) ::: List( o )
}

object regularize {
  def apply( p: LKProof ) : LKProof = rec( p, new EmptySet )._1

  def rec( p: LKProof, vars: Set[HOLVar] ) : (LKProof, Set[HOLVar], Map[FormulaOccurrence, FormulaOccurrence] ) = 
  {
    val ret = p match
    {
      // FIXME: cast!?!
      case r @ CutRule( p1, p2, _, a1, a2 ) => handleBinary( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, vars, CutRule.apply )
      case r @ AndRightRule( p1, p2, _, a1, a2, _ ) => handleBinary( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, vars, AndRightRule.apply )
      case r @ OrLeftRule( p1, p2, _, a1, a2, _ ) => handleBinary( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, vars, OrLeftRule.apply )
      case r @ ImpLeftRule( p1, p2, _, a1, a2, _ ) => handleBinary( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, vars, ImpLeftRule.apply )
      case r @ EquationLeft1Rule( p1, p2, _, a1, a2, m ) => handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationLeft1Rule.apply )
      case r @ EquationLeft2Rule( p1, p2, _, a1, a2, m ) => handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationLeft2Rule.apply )
      case r @ EquationRight1Rule( p1, p2, _, a1, a2, m ) => handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationRight1Rule.apply )
      case r @ EquationRight2Rule( p1, p2, _, a1, a2, m ) => handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationRight2Rule.apply )
   }
   ( ret._1, vars, ret._2 )
 }

  def handleEquational( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m :Formula, vars: Set[HOLVar],
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, Formula) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1, vars )
      val rec2 = rec( p2, vars ++ rec1._2 )
      val map = rec1._3 ++ rec2._3
      val new_proof = constructor( r.uProof1, r.uProof2, map( r.aux.head.head ), map( r.aux.tail.head.head ), m )
      ( new_proof, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._3 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._3 ) )
  }

  def handleBinary( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, vars: Set[HOLVar],
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1, vars )
      val rec2 = rec( p2, vars ++ rec1._2 )
      val map = rec1._3 ++ rec2._3
      val new_proof = constructor( r.uProof1, r.uProof2, map( r.aux.head.head ), map( r.aux.tail.head.head ) )
      ( new_proof, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._3 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._3 ) )
  }

  // FIXME: adapted from LKtoLKskc!
  def computeMap( occs: Set[FormulaOccurrence], old_proof: LKProof, 
                  new_proof: LKProof, old_map : Map[FormulaOccurrence, FormulaOccurrence]) =
  {
    val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get, 
      new_proof.getDescendantInLowerSequent( old_map(fo) ).get ) )
    map
  }

}
