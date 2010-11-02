/*
 * base.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lksk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import scala.collection.immutable.Set
import scala.collection.immutable.{Map,HashMap}

import at.logic.calculi.lk.base.{FormulaNotExistsException,AuxiliaryFormulas,PrincipalFormulas,Sequent,SequentOccurrence}
import at.logic.calculi.occurrences._

package base {
  object TypeSynonyms {
    type Label = Set[HOLExpression]
    object EmptyLabel {
      def apply() = Set[HOLExpression]()
    }
  }

  import TypeSynonyms._

  class LabelledFormulaOccurrence (override val formula: HOLFormula,
                                   override val ancestors: List[LabelledFormulaOccurrence],
                                   val label: Label) extends FormulaOccurrence( formula, ancestors ) {
    def factory: FOFactory = LKskFOFactory
    override def toString: String = formula.toString + " (label: " + label.toString + ")"
  }

  private[lksk] object LKskFOFactory extends FOFactory {
    def createPrincipalFormulaOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence]) = {
      assert( ancestors.forall( _.isInstanceOf[LabelledFormulaOccurrence] ) )
      createOccurrence(formula, ancestors.asInstanceOf[List[LabelledFormulaOccurrence]])
    }
    def createContextFormulaOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence]) = {
      assert( ancestors.forall( _.isInstanceOf[LabelledFormulaOccurrence] ) )
      createOccurrence(formula, ancestors.asInstanceOf[List[LabelledFormulaOccurrence]])
    }
    def createOccurrence(formula: HOLFormula, ancestors: List[LabelledFormulaOccurrence]) = {
      val l = ancestors.head.label
      assert( ancestors.forall( a => a.label == l ) )
      new LabelledFormulaOccurrence(formula, ancestors, l)
    }
    // when creating a main formula for a weak quantifier inference in LKsk, we may choose
    // whether to delete the term from the label, or not. If deletion is not desired,
    // term should be set to None.
    def createWeakQuantMain(formula: HOLFormula, ancestor: LabelledFormulaOccurrence, term: Option[HOLExpression]) =
    {
      val newlabel = term match {
        case None => ancestor.label
        case Some(x) => ancestor.label - x
      }
      new LabelledFormulaOccurrence(formula, ancestor::Nil, newlabel )
    }
    def createInitialOccurrence(formula: HOLFormula, label: Label) =
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

  object sequentOccurrenceToLabelledSequentOccurrence {
    def apply( s: SequentOccurrence ) = new LabelledSequentOccurrence( s.antecedent.asInstanceOf[Set[LabelledFormulaOccurrence]],
                                                                       s.succedent.asInstanceOf[Set[LabelledFormulaOccurrence]] )
  }
}
