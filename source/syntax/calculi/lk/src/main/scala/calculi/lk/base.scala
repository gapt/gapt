/*
 * base.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap


package base {

  private[lk] object LKFOFactory extends FOFactory {
    def createPrincipalFormulaOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence]) = createOccurrence(formula, ancestors)
    def createContextFormulaOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence]) = createOccurrence(formula, ancestors)
    def createOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence]) = new FormulaOccurrence(formula, ancestors) {def factory = LKFOFactory}
  }

  // List should be changed into multiset (I am not sure anymore as we need to map formula occurrences also in the original sequent.
  // For eaxmple when duplicating a branch we want to be able to know which formula is mapped to which)
  class Sequent(val antecedent: List[HOLFormula], val succedent: List[HOLFormula])
  {
    val ant = antecedent.sort((x1,x2) => x1.toString < x2.toString)
    val suc = succedent.sort((x1,x2) => x1.toString < x2.toString)
    // The two parts of the sequent are ordered lexicographically so equal denotes multiset equals
    override def equals( o: Any ) = o match {
      case os : Sequent => ant == os.ant && suc == os.suc
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
    def toStringSimple : String = antecedent.foldRight("")( (f, str) => str + ", " + f.toStringSimple ) + " :- " +
                                  succedent.foldRight("")( (f, str) => str + ", " + f.toStringSimple )
  }
  object Sequent {
    def apply(antecedent: List[HOLFormula], succedent: List[HOLFormula]) = new Sequent(antecedent, succedent)
    def unapply(s: Sequent) = Some(s.antecedent, s.succedent)
  }
  // List should be changed into set
  case class SequentOccurrence(antecedent: Set[FormulaOccurrence], succedent: Set[FormulaOccurrence])
  {
    def getSequent = Sequent( antecedent.toList.map( fo => fo.formula ), succedent.toList.map( fo => fo.formula ) )
    def multisetEquals( o: SequentOccurrence ) = getSequent.multisetEquals(o.getSequent)
    //def multisetEquals( o: SequentOccurrence ) = (((antecedent.toList.map(x => x.formula)) == o.antecedent.toList.map(x => x.formula)) && ((succedent.toList.map(x => x.formula)) == o.succedent.toList.map(x => x.formula)))
    override def toString : String = SequentFormatter.sequentOccurenceToString(this)
  }

  // exceptions
  class LKRuleException(msg: String) extends RuleException(msg)
  class LKRuleCreationException(msg: String) extends LKRuleException(msg)
  class FormulaNotExistsException(msg: String) extends LKRuleException(msg)

   trait LKProof extends Proof[SequentOccurrence]{
    def getDescendantInLowerSequent(fo: FormulaOccurrence): Option[FormulaOccurrence] = {
      (root.antecedent ++ root.succedent).filter(x => x.ancestors.contains(fo)).toList match {
        case x::Nil => Some(x)
        case Nil => None
        case _ => throw new LKRuleException("Illegal lower sequent in rule in application of getDescendantInLowerSequent: More than one such formula exists")
      }
    }
  }
  trait UnaryLKProof extends UnaryTree[SequentOccurrence] with LKProof with UnaryProof[SequentOccurrence] {
    override def uProof = t.asInstanceOf[LKProof]
  }
  trait BinaryLKProof extends BinaryTree[SequentOccurrence] with LKProof with BinaryProof[SequentOccurrence] {
    override def uProof1 = t1.asInstanceOf[LKProof]
    override def uProof2 = t2.asInstanceOf[LKProof]
  }

  // traits denoting having auxiliary and main formulas
  trait AuxiliaryFormulas {
    // for each upper sequent we have a list of occurrences
    def aux: List[List[FormulaOccurrence]]
  }
  trait PrincipalFormulas {
    def prin: List[FormulaOccurrence]
  }
  trait SubstitutionTerm {
    def subst: HOLExpression
  }
  trait Eigenvariable {
    def eigenvar: HOLVar
  }

  // method for creating the context of the lower sequent. Essentially creating nre occurrences
  // create new formula occurrences in the new context
  object createContext { def apply(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => x.factory.createContextFormulaOccurrence(x.formula, x::Nil)) }

  object SequentFormatter {
    //formats a lambda term to a readable string, dropping the types and printing binary function symbols infix
    def formulaToString(f:LambdaExpression) : String = {
        f match {
            case App(App(Var(name,t),x),y)    => "(" + formulaToString(x) + " "+ name.toString()+ " " +formulaToString(y) +")"
            case App(x,y)    => formulaToString(x) + "("+ formulaToString(y) +")"
            case Var(name,t) => name.toString()
            case Abs(x,y)    => formulaToString(x)+".("+formulaToString(y)+")"
            case  x : Any    => "(unmatched class: "+x.getClass() + ")"
                //            case _ => "(argl!!!)"
        }
    }

    // formats a sequent to a readable string
    def sequentToString(s : Sequent) : String = {
        var sb = new scala.StringBuilder()
        var first = true
        for (f <- s.antecedent) {
            if (! first) sb.append(", ")
            else first = false

            sb.append(formulaToString(f))
        }
        sb.append(" :- ")
        first =true
        for (f <- s.succedent) {
            if (! first) sb.append(", ")
            else first = false
            sb.append(formulaToString(f))

        }
        sb.toString
    }

    def sequentOccurenceToString(s: SequentOccurrence) : String = sequentToString(s.getSequent)

  }

}
