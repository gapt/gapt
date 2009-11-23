/*
 * base.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.language.hol.propositions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap

package base {

  // List should be changed into multiset (I am not sure anymore as we need to map formula occurrences also in the original sequent.
  // For eaxmple when duplicating a branch we want to be able to know which formula is mapped to which)
  case class Sequent(antecedent: List[Formula], succedent: List[Formula])
  {
    // equality defined by equality on antecedent and succedent *lists*
    // perhaps defining it on multisets is more suitable?
    override def equals( o: Any ) = o match {
      case os : Sequent => antecedent == os.antecedent && succedent == os.succedent
      case _ => false
    }
    // TODO: use multisets in implementation!
    def multisetEquals( o: Sequent ) = {
      def updater( f: Formula, mt: HashMap[Formula, Int]) =
        if (!mt.contains(f)) mt.put( f, 1 ) else mt.update( f, mt.apply( f ) + 1 )
      val mt = new HashMap[Formula, Int]
      antecedent.foreach( f => updater( f, mt ) )
      val mo = new HashMap[Formula, Int]
      o.antecedent.foreach( f => updater( f, mo ) )
      if ( mt != mo )
        false
      mt.clear
      mo.clear
      succedent.foreach( f => updater( f, mt ) )
      o.succedent.foreach( f => updater( f, mo ) )
      mt == mo
    }
    override def toString : String = antecedent.toString + " :- " + succedent.toString
  }
  // List should be changed into set
  case class SequentOccurrence(antecedent: Set[FormulaOccurrence], succedent: Set[FormulaOccurrence])
  {
    def getSequent = Sequent( antecedent.toList.map( fo => fo.formula ), succedent.toList.map( fo => fo.formula ) )
    def multisetEquals( o: SequentOccurrence ) = getSequent.multisetEquals(o.getSequent)
    //def multisetEquals( o: SequentOccurrence ) = (((antecedent.toList.map(x => x.formula)) == o.antecedent.toList.map(x => x.formula)) && ((succedent.toList.map(x => x.formula)) == o.succedent.toList.map(x => x.formula)))
  }

  // exceptions
  class LKRuleException(msg: String) extends Exception(msg)
  class LKRuleCreationException(msg: String) extends LKRuleException(msg)
  class FormulaNotExistsException(msg: String) extends LKRuleException(msg)

  abstract class RuleTypeA
  abstract class NullaryRuleTypeA extends RuleTypeA
  abstract class UnaryRuleTypeA extends RuleTypeA
  abstract class BinaryRuleTypeA extends RuleTypeA

  trait LKProof extends Tree[SequentOccurrence] {
    def root = vertex
    def rule: RuleTypeA
    def getDescendantInLowerSequent(fo: FormulaOccurrence): Option[FormulaOccurrence] = {
      val set = getOccurrence(fo.label, (root.antecedent ++ root.succedent)) // double casting because set is invariant in the type parameter
      set.toList match {
        case x::Nil if x.ancestors.contains(fo) => Some(x)
        case _ => None
      }
    }
    def getOccurrence(o: Occur, set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.filter(x => x.label == o)
  }
  trait UnaryLKProof extends UnaryTree[SequentOccurrence] with LKProof {
    def uProof = t.asInstanceOf[LKProof]
  }
  trait BinaryLKProof extends BinaryTree[SequentOccurrence] with LKProof {
    def uProof1 = t1.asInstanceOf[LKProof]
    def uProof2 = t2.asInstanceOf[LKProof]
  }

  // traits denoting having auxiliary and main formulas
  trait AuxiliaryFormulas {
    // for each upper sequent we have a list of occurrences
    def aux: List[List[FormulaOccurrence]]
  }
  trait PrincipalFormulas {
    def prin: List[FormulaOccurrence]
  }

  // method for creating the context of the lower sequent. Essentially creating nre occurrences
  // create new formula occurrences in the new context
  object createContext { def apply(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => FormulaOccurrence(x.formula, x)) }
}
