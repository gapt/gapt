/*
 * base.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lksk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol.propositions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.{Set,EmptySet}
import scala.collection.mutable.{Map,HashMap}
import at.logic.language.lambda.typedLambdaCalculus.LambdaExpression

import at.logic.calculi.lk.base.{FormulaNotExistsException,AuxiliaryFormulas,PrincipalFormulas,Sequent}

package base {
  object TypeSynonyms {
    type Label = Set[LambdaExpression]
    object EmptyLabel {
      def apply() = new EmptySet[LambdaExpression]
    }
  }

  import TypeSynonyms._

  case class LabelledSequentOccurrence(antecedent: Set[FormulaOccurrence], succedent: Set[FormulaOccurrence], map: Map[FormulaOccurrence,Label])
  {
    def getSequent = Sequent( antecedent.toList.map( fo => fo.formula ), succedent.toList.map( fo => fo.formula ) )
    def ++( that: LabelledSequentOccurrence ) = LabelledSequentOccurrence( antecedent ++ that.antecedent, succedent ++ that.succedent, map ++ that.map )
  }

  // exceptions
  class LKskRuleException(msg: String) extends RuleException(msg)
  class LKskRuleCreationException(msg: String) extends LKskRuleException(msg)

   trait LKskProof extends Proof[LabelledSequentOccurrence]{
    def getDescendantInLowerSequent(fo: FormulaOccurrence): Option[FormulaOccurrence] = {
      (root.antecedent ++ root.succedent).filter(x => x.ancestors.contains(fo)).toList match {
        case x::Nil => Some(x)
        case Nil => None
        case _ => throw new LKskRuleException("Illegal lower sequent in rule in application of getDescendantInLowerSequent: More than one such formula exists")
      }
    }
  }
  trait UnaryLKskProof extends UnaryTree[LabelledSequentOccurrence] with LKskProof with UnaryProof[LabelledSequentOccurrence] {
    override def uProof = t.asInstanceOf[LKskProof]
  }
  trait BinaryLKskProof extends BinaryTree[LabelledSequentOccurrence] with LKskProof with BinaryProof[LabelledSequentOccurrence] {
    override def uProof1 = t1.asInstanceOf[LKskProof]
    override def uProof2 = t2.asInstanceOf[LKskProof]
  }

  object createLeftContext {
    def apply(set: Set[FormulaOccurrence], map: Map[FormulaOccurrence, Label]): LabelledSequentOccurrence = 
    {
      val newmap = new HashMap[FormulaOccurrence, Label]
      val newset = set.map(x => {
        val newx = x.factory.createContextFormulaOccurrence(x.formula, x::Nil)
        newmap.update( newx, map.apply( x ) )
        newx
      })
      LabelledSequentOccurrence( newset, new EmptySet, newmap )
    }
  }

  object createRightContext {
    def apply(set: Set[FormulaOccurrence], map: Map[FormulaOccurrence, Label]): LabelledSequentOccurrence = 
    {
      val newmap = new HashMap[FormulaOccurrence, Label]
      val newset = set.map(x => {
        val newx = x.factory.createContextFormulaOccurrence(x.formula, x::Nil)
        newmap.update( newx, map.apply( x ) )
        newx
      })
      LabelledSequentOccurrence( new EmptySet, newset, newmap )
    }
  }
}
