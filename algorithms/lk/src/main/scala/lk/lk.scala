package at.logic.algorithms.lk

import scala.collection.immutable.Set

import at.logic.calculi.lk.propositionalRules.{Axiom, CutRule}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}

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
    }
  def getAncestors( o: FormulaOccurrence ) : List[FormulaOccurrence] =
    o.ancestors.flatMap( a => getAncestors( a ) ) ::: List( o )
}

