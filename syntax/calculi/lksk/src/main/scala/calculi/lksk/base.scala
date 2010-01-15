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
import scala.collection.immutable.{Map,HashMap}

import at.logic.calculi.lk.base.{FormulaNotExistsException,AuxiliaryFormulas,PrincipalFormulas,Sequent,SequentOccurrence}
import at.logic.calculi.occurrences._
import at.logic.language.hol.propositions.TypeSynonyms._

package base {
  object TypeSynonyms {
    type Label = Set[HOLTerm]
    object EmptyLabel {
      def apply() = new EmptySet[HOLTerm]
    }
  }

  import TypeSynonyms._

  class LabelledFormulaOccurrence (override val formula: Formula, 
                                   override val ancestors: List[LabelledFormulaOccurrence],
                                   val label: Label) extends FormulaOccurrence( formula, ancestors ) {
    def factory: FOFactory = LKskFOFactory
    override def toString: String = formula.toString + " (label: " + label.toString + ")"
  }

  private[lksk] object LKskFOFactory extends FOFactory {
    def createPrincipalFormulaOccurrence(formula: Formula, ancestors: List[FormulaOccurrence]) = {
      assert( ancestors.forall( _.isInstanceOf[LabelledFormulaOccurrence] ) )
      createOccurrence(formula, ancestors.asInstanceOf[List[LabelledFormulaOccurrence]])
    }
    def createContextFormulaOccurrence(formula: Formula, ancestors: List[FormulaOccurrence]) = {
      assert( ancestors.forall( _.isInstanceOf[LabelledFormulaOccurrence] ) )
      createOccurrence(formula, ancestors.asInstanceOf[List[LabelledFormulaOccurrence]])
    }
    def createOccurrence(formula: Formula, ancestors: List[LabelledFormulaOccurrence]) = {
      val l = ancestors.first.label
      assert( ancestors.forall( a => a.label == l ) )
      new LabelledFormulaOccurrence(formula, ancestors, l)
    }
    // when creating a main formula for a weak quantifier inference in LKsk, we may choose
    // whether to delete the term from the label, or not. If deletion is not desired,
    // term should be set to None.
    def createWeakQuantMain(formula: Formula, ancestor: LabelledFormulaOccurrence, term: Option[HOLTerm]) =
    {
      val newlabel = term match {
        case None => ancestor.label
        case Some(x) => ancestor.label - x
      }
      new LabelledFormulaOccurrence(formula, ancestor::Nil, newlabel )
    }
    def createInitialOccurrence(formula: Formula, label: Label) =
      new LabelledFormulaOccurrence( formula, Nil, label )
  }

  // TODO: instead of l_antecedent, use override val antecedent
  // does not work right now because Set is not covariant!
  class LabelledSequentOccurrence(val l_antecedent: Set[LabelledFormulaOccurrence],
                                  val l_succedent: Set[LabelledFormulaOccurrence])
    extends SequentOccurrence( l_antecedent.asInstanceOf[Set[FormulaOccurrence]],
                               l_succedent.asInstanceOf[Set[FormulaOccurrence]] ) {
    override def toString: String = l_antecedent.toString + " :- " + l_succedent.toString
  }
}
