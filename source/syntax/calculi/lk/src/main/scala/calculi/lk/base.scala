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

package base {

import collection.immutable.Seq

/*
import java.util.Comparator

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
      // TODO: quicksort does not work without the cast??? No... quicksort is defined for Arrays and apparently Lists
      // and Arrays are not related (scala.Array and scala.collection.immutable.List)

      object LambdaComparator extends Comparator[LambdaExpression] {
        override def compare(exp1 : LambdaExpression, exp2: LambdaExpression) : Int = {
          val s1 : String = exp1.toString
          val s2 : String = exp2.toString
          s1.compare(s2)
        }

      }

      quickSort[LambdaExpression]( ant.asInstanceOf[Array[LambdaExpression]] ) (comparatorToOrdering(LambdaComparator))
      quickSort[LambdaExpression]( succ.asInstanceOf[Array[LambdaExpression]] ) (comparatorToOrdering(LambdaComparator))
      Sequent( ant.toList, succ.toList )
    }
  }

  object Sequent {
    def apply(antecedent: List[HOLFormula], succedent: List[HOLFormula]) = new Sequent(antecedent, succedent)
    def unapply(s: Sequent) = Some(s.antecedent, s.succedent)
  }

  object substitute {
    // TODO: write a substitution function that knows that
    // HOLFormula is closed under substitution
    def apply(sub: Substitution[HOLExpression], seq: Sequent) =
      Sequent( seq.antecedent.map(f => sub(f).asInstanceOf[HOLFormula]), seq.succedent.map(f => sub(f).asInstanceOf[HOLFormula]) )
  }
  */

  class Sequent(val antecedent: Seq[FormulaOccurrence], val succedent: Seq[FormulaOccurrence])
  {
    //TODO improve both equals methods
    def multisetEquals( o: Sequent ) = o.antecedent.diff(antecedent).isEmpty &&
                                       o.succedent.diff(succedent).isEmpty &&
                                       antecedent.diff(o.antecedent).isEmpty &&
                                       succedent.diff(o.succedent).isEmpty
    def setEquals(o: Sequent ) = antecedent.forall(a => o.antecedent.contains(a)) &&
                                 succedent.forall(a => o.succedent.contains(a)) &&
                                 o.antecedent.forall(a => antecedent.contains(a)) &&
                                 o.succedent.forall(a => succedent.contains(a))
    override def toString : String = SequentFormatter.sequentToString(this)
    def removeFormulasAtOccurrences(occs: Seq[FormulaOccurrence]): Sequent = Sequent(
        antecedent.filterNot(x => occs.contains(x)),
        succedent.filterNot(x => occs.contains(x))
      )
    def getChildOf(fo: FormulaOccurrence): Option[FormulaOccurrence] = (antecedent ++ succedent).find(_.ancestors.contains(fo))
    //override def toString : String = antecedent.toString + " :- " + succedent.toString
    def toStringSimple : String = antecedent.foldRight("")( (f, str) => str + ", " + f.toStringSimple ) + " :- " +
                                  succedent.foldRight("")( (f, str) => str + ", " + f.toStringSimple )
  }

  object Sequent {
    def apply(antecedent: Seq[FormulaOccurrence], succedent: Seq[FormulaOccurrence]) = new Sequent(antecedent, succedent)
    def unapply(so: Sequent) = Some(so.antecedent, so.succedent)
  }

  // exceptions
  class LKRuleException(msg: String) extends RuleException(msg)
  class LKRuleCreationException(msg: String) extends LKRuleException(msg)
  class FormulaNotExistsException(msg: String) extends LKRuleException(msg)

  trait LKProof extends TreeProof[Sequent] with Tree[Sequent] {
    def getDescendantInLowerSequent(fo: FormulaOccurrence): Option[FormulaOccurrence] = {
      (root.antecedent ++ root.succedent).filter(x => x.ancestors.find(y => y =^ fo) != None) match {
        case x::Nil => Some(x)
        case Nil => None
        case _ => throw new LKRuleException("Illegal lower sequent in rule in application of getDescendantInLowerSequent: More than one such formula exists")
      }
    }
  }
  trait NullaryLKProof extends LeafTree[Sequent] with LKProof with NullaryTreeProof[Sequent]
  trait UnaryLKProof extends UnaryTree[Sequent] with LKProof with UnaryTreeProof[Sequent] {
    override def uProof = t.asInstanceOf[LKProof]
  }
  trait BinaryLKProof extends BinaryTree[Sequent] with LKProof with BinaryTreeProof[Sequent] {
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
    def apply(set: Seq[FormulaOccurrence]): Seq[FormulaOccurrence] = set.map(x => FormulaOccurrence(x,x::Nil))
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
  }

}
