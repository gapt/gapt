/*
 * base.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.treeProofs._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import scala.util.Sorting.quickSort
import scala.math.Ordering._

package base {

  // a trait for all objects that have a sequent (or its descendant) component (like Sequent, SequentOccurrence
  // the root of a proof, etc.) It can be used in algorithms that expect a sequent
  trait SequentLike  {
    def getSequent: Sequent
  }

  // List should be changed into multiset (I am not sure anymore as we need to map formula occurrences also in the original sequent.
  // For example when duplicating a branch we want to be able to know which formula is mapped to which)
  class Sequent(val antecedent: List[HOLFormula], val succedent: List[HOLFormula]) extends SequentLike
  {
    val ant = antecedent.sortWith((x1,x2) => x1.toString < x2.toString)
    val suc = succedent.sortWith((x1,x2) => x1.toString < x2.toString)
    // The two parts of the sequent are ordered lexicographically so equal denotes multiset equals
    override def equals( o: Any ) = o match {
      case os : Sequent => ant == os.ant && suc == os.suc
      case _ => false
    }
    def getSequent = this
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
    def setEquals( o: Sequent ) = // to improve!
      antecedent.forall(a => o.antecedent.contains(a)) &&
      succedent.forall(a => o.succedent.contains(a)) &&
      o.antecedent.forall(a => antecedent.contains(a)) &&
      o.succedent.forall(a => succedent.contains(a))
    //override def toString : String = antecedent.toString + " :- " + succedent.toString
    def toStringSimple : String = antecedent.foldRight("")( (f, str) => str + ", " + f.toStringSimple ) + " :- " +
                                  succedent.foldRight("")( (f, str) => str + ", " + f.toStringSimple )
    // returns the n literal of the sequent considering that the literals are ordered antecedent ++ succedent
    def apply(n: Int) = if (n < antecedent.size) antecedent(n) else succedent(n - antecedent.size)
    override def toString =
      (if (antecedent.size > 1) antecedent.head.toString + antecedent.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else antecedent.foldLeft("")((s,a) => s+a.toString)) + ":-" +
      (if (succedent.size > 1) succedent.head.toString + succedent.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else succedent.foldLeft("")((s,a) => s+a.toString))
    def removeFormulasAtIndices(inds: Seq[Int]): Sequent = Sequent(
        antecedent.zipWithIndex.filter(x => !inds.contains(x._2)).map(x => x._1),
        succedent.zipWithIndex.filter(x => !inds.contains(x._2 + antecedent.size)).map(x => x._1)
      )
    def toFormula = Or( antecedent.map( f => Neg( f ) ) ::: succedent )
    // checks whether this sequent is of the form F :- F
    def isTaut = antecedent.size == 1 && succedent.size == 1 && antecedent.head == succedent.head

    def getOrderedSequent = {
      val ant = antecedent.toArray
      val succ = succedent.toArray
      // TODO: quicksort does not work without the cast???
      quickSort[LambdaExpression]( ant.asInstanceOf[Array[LambdaExpression]] )
      quickSort[LambdaExpression]( succ.asInstanceOf[Array[LambdaExpression]] )
      Sequent( ant.toList, succ.toList )
    }
  }
  object Sequent {
    def apply(antecedent: List[HOLFormula], succedent: List[HOLFormula]) = new Sequent(antecedent, succedent)
    def unapply(s: Sequent) = Some(s.antecedent, s.succedent)
  }
  // List should be changed into set
  class SequentOccurrence(val antecedent: Set[FormulaOccurrence], val succedent: Set[FormulaOccurrence]) extends SequentLike
  {
    def getSequent = Sequent( antecedent.toList.map( fo => fo.formula ), succedent.toList.map( fo => fo.formula ) )

    def multisetEquals( o: SequentOccurrence ) = getSequent.multisetEquals(o.getSequent)
    def multisetEquals( o: Sequent ) = getSequent.multisetEquals(o)
    def setEquals(o: SequentOccurrence ) = getSequent.setEquals(o.getSequent)
    def setEquals( o: Sequent ) = getSequent.setEquals(o)
    //def multisetEquals( o: SequentOccurrence ) = (((antecedent.toList.map(x => x.formula)) == o.antecedent.toList.map(x => x.formula)) && ((succedent.toList.map(x => x.formula)) == o.succedent.toList.map(x => x.formula)))
    override def toString : String = SequentFormatter.sequentOccurenceToString(this)
    def removeFormulasAtOccurrences(occs: Seq[FormulaOccurrence]): SequentOccurrence = SequentOccurrence(
        antecedent.filterNot(x => occs.contains(x)),
        succedent.filterNot(x => occs.contains(x))
      )
    def getChildOf(fo: FormulaOccurrence): Option[FormulaOccurrence] = (antecedent ++ succedent).find(_.ancestors.contains(fo))
  }
  object SequentOccurrence {
    def apply(antecedent: Set[FormulaOccurrence], succedent: Set[FormulaOccurrence]) = new SequentOccurrence(antecedent, succedent)
    def unapply(so: SequentOccurrence) = Some(so.antecedent, so.succedent)
  }

  // exceptions
  class LKRuleException(msg: String) extends RuleException(msg)
  class LKRuleCreationException(msg: String) extends LKRuleException(msg)
  class FormulaNotExistsException(msg: String) extends LKRuleException(msg)

  trait LKProof extends TreeProof[SequentOccurrence] with Tree[SequentOccurrence] with SequentLike {
    def getDescendantInLowerSequent(fo: FormulaOccurrence): Option[FormulaOccurrence] = {
      (root.antecedent.toList ++ root.succedent.toList).filter(x => x.ancestors.find(y => y =^ fo) != None) match {
        case x::Nil => Some(x)
        case Nil => None
        case _ => throw new LKRuleException("Illegal lower sequent in rule in application of getDescendantInLowerSequent: More than one such formula exists")
      }
    }
    def getSequent = root.getSequent
  }
  trait NullaryLKProof extends LeafTree[SequentOccurrence] with LKProof with NullaryTreeProof[SequentOccurrence]
  trait UnaryLKProof extends UnaryTree[SequentOccurrence] with LKProof with UnaryTreeProof[SequentOccurrence] {
    override def uProof = t.asInstanceOf[LKProof]
  }
  trait BinaryLKProof extends BinaryTree[SequentOccurrence] with LKProof with BinaryTreeProof[SequentOccurrence] {
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
  object createContext {
    def apply(set: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => x.factory.createContextFormulaOccurrence(x.formula, x, x::Nil, set - x))
    def apply(set: Set[FormulaOccurrence], binary: Set[FormulaOccurrence]): Set[FormulaOccurrence] = set.map(x => x.factory.createContextFormulaOccurrence(x.formula, x, x::Nil, set - x, binary))
  }

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
