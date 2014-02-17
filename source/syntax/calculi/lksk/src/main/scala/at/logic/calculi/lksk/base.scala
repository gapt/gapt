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
import at.logic.language.lambda.substitutions._
import scala.collection.immutable.HashMap

import at.logic.calculi.lk.base.{FormulaNotExistsException,AuxiliaryFormulas,PrincipalFormulas,Sequent}
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
                                   val skolem_label: Label) extends FormulaOccurrence( formula, ancestors, LKskFOFactory ) {
    //override def factory = LKskFOFactory
    override def toString: String = formula.toString + " (label: " + skolem_label.toString + ")"

  }

  object LabelledFormulaOccurence {
    implicit def lfo2fo(s : LabelledFormulaOccurrence) : HOLFormula = s.formula

    def unapply(fo : LabelledFormulaOccurrence) = Some(fo.formula, fo.ancestors, fo.skolem_label)
  }




  //private[lksk] 
  object LKskFOFactory extends FOFactory {
    override def createFormulaOccurrence(formula: HOLFormula, ancestors: Seq[FormulaOccurrence]): FormulaOccurrence = {
      if (ancestors.forall(_.isInstanceOf[LabelledFormulaOccurrence]))
        createOccurrence(formula, (ancestors.asInstanceOf[Seq[LabelledFormulaOccurrence]]).toList )
      else //TODO: we can not check if the label is unchanged in unlabelled ancestors
        throw new Exception("ancestors not labelled "+ancestors.filterNot(_.isInstanceOf[LabelledFormulaOccurrence]).mkString("(",",",")"))
    }

    def createContextFormulaOccurrenceWithSubst(formula: HOLFormula, current: FormulaOccurrence, ancestors: List[FormulaOccurrence], sub: Substitution[HOLExpression]) = {
      assert( ancestors.forall( _.isInstanceOf[LabelledFormulaOccurrence] ) )
      val l_ancestors = ancestors.map( _.asInstanceOf[LabelledFormulaOccurrence] )
      val l = l_ancestors.head.skolem_label
      assert( l_ancestors.forall( a => a.skolem_label == l ) )
      new LabelledFormulaOccurrence(sub(formula).asInstanceOf[HOLFormula], l_ancestors, l.map( sub(_) ) )
    }

    def createOccurrence(formula: HOLFormula, ancestors: List[LabelledFormulaOccurrence]) : LabelledFormulaOccurrence = {
      val l = ancestors.head.skolem_label
      if(! ancestors.forall( a => a.skolem_label == l ))
        throw new Exception("Error creating labelled formula occurrence: ancestor labels of "+l+" do not agree: "+ancestors.map(_.skolem_label).mkString(",") )
      new LabelledFormulaOccurrence(formula, ancestors, l)
    }

    // when creating a main formula for a weak quantifier inference in LKsk, we may choose
    // whether to delete the term from the label, or not. If deletion is not desired,
    // term should be set to None.
    def createWeakQuantMain(formula: HOLFormula, ancestor: LabelledFormulaOccurrence, term: Option[HOLExpression]) =
    {
      val newlabel = term match {
        case None => ancestor.skolem_label
        case Some(x) => ancestor.skolem_label - x
      }
      new LabelledFormulaOccurrence(formula, ancestor::Nil, newlabel )
    }

    def createInitialOccurrence(formula: HOLFormula, label: Label) =
      new LabelledFormulaOccurrence( formula, Nil, label )

    }

  // TODO: instead of l_antecedent, use override val antecedent
  // does not work right now because Set is not covariant!
  class LabelledSequent(val l_antecedent: Seq[LabelledFormulaOccurrence],
                                  val l_succedent: Seq[LabelledFormulaOccurrence])
    extends Sequent( l_antecedent.asInstanceOf[Seq[FormulaOccurrence]],
                               l_succedent.asInstanceOf[Seq[FormulaOccurrence]] ) {
    override def toString: String = l_antecedent.toString + " :- " + l_succedent.toString
  }


  object sequentToLabelledSequent {
    def apply( s: Sequent ) = new LabelledSequent( s.antecedent.asInstanceOf[Seq[LabelledFormulaOccurrence]],
                                                   s.succedent.asInstanceOf[Seq[LabelledFormulaOccurrence]] )
  }
}
