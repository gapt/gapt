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

import at.logic.utils.traits.Occurrence
import at.logic.language.lambda.substitutions.Substitution

import java.util.Comparator
import scala.math.Ordering._
import tools.nsc.settings.FscSettings
import base.types._

  package types {
    object implicits {
      implicit def pair2fsequent(fs:(Seq[HOLFormula], Seq[HOLFormula])) = new FSequent(fs._1,fs._2)
    }

    class FSequent(val antecedent : Seq[HOLFormula], val succedent : Seq[HOLFormula]) {
      val _1 = antecedent
      val _2 = succedent
      
      override def equals(fs : Any) : Boolean = fs match {
        case FSequent(ant,succ) => (this.antecedent equals ant) && (this.succedent equals succ)
        case _ => false
      }

      override def toString() = FSequent.toString((x:HOLFormula) => x.toString, this)

      def setEquals(g:FSequent) = FSequent.setEquals(this, g)
      def multiSetEquals(g:FSequent) = FSequent.multiSetEquals(this, g)
      def formulas : Seq[HOLFormula] = antecedent ++ succedent

      /*
       compose constructs a sequent from two sequents. Corresponds to the 'o' operator in CERes
      */
      def compose(other: FSequent) = FSequent(antecedent ++ other.antecedent, succedent ++ other.succedent)
    }
  }

  object FSequent {
    def apply(ant: Seq[HOLFormula], succ: Seq[HOLFormula]) : types.FSequent =  new FSequent(ant,succ) //Pair(ant, succ)
    def apply(seq : Sequent) : types.FSequent = FSequent(seq.antecedent map (_.formula), seq.succedent map (_.formula))

    def unapply(f: FSequent) : Option[(Seq[HOLFormula], Seq[HOLFormula])] = Some( (f.antecedent, f.succedent) )

    private def lst2string[T](fun:(T=>String), seperator: String, l:List[T]) : String = l match {
      case Nil => ""
      case List(x) => fun(x)
      case x::xs => fun(x)  + seperator + lst2string(fun, seperator, xs)
    }

    def toString(formatter: HOLFormula => String,formulas : Seq[HOLFormula]) : String = lst2string( formatter, ", ", formulas.toList )

    def toString(formatter : HOLFormula => String ,f : FSequent)  : String  = "(" + toString(formatter,f._1) + " :- "  + toString(formatter,f._2) + ")"

    def toStringSimple(formulas : Seq[HOLFormula])  : String = toString( (x:HOLFormula) => x.toStringSimple, formulas.toList )
    def toStringSimple(f : FSequent)  : String  = toString((x:HOLFormula) => x.toStringSimple,f )

    def setEquals(f: FSequent, g: FSequent) : Boolean =
        Set(f._1) == Set(g._1) &&
        Set(f._2) == Set(g._2)

    def multiSetEquals(f : FSequent, g : FSequent) : Boolean =
          f._1.diff(g._1).isEmpty && f._2.diff(g._2).isEmpty &&
          g._1.diff(f._1).isEmpty && g._2.diff(f._2).isEmpty

  }

  import types._

  object substitute {
    // TODO: write a substitution function that knows that
    // HOLFormula is closed under substitution
    def apply(sub: Substitution[HOLExpression], pair: FSequent) =
      FSequent( pair._1.map(f => sub(f).asInstanceOf[HOLFormula]), pair._2.map(f => sub(f).asInstanceOf[HOLFormula] ))
  }


  class Sequent(val antecedent: Seq[FormulaOccurrence], val succedent: Seq[FormulaOccurrence])
  {
    /*
    require(checkFormulaOccurrences(antecedent), 
      //"\nERROR: Antecedent contains binding errors: " + (antecedent map (_.formula.toStringSimple)))
      "\nERROR: Antecedent contains binding errors: " + antecedent)
    require(checkFormulaOccurrences(succedent),  
      "\nERROR: Succedent contains binding errors: " + (succedent map (_.formula.toStringSimple)))
    */

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
    override def equals(o: Any) = o match {
      case s: Sequent => multisetEquals(s)
      case _ => false
    }
    // compares the multiset of formulas
    def syntacticMultisetEquals(o: Sequent ) = {
      val ta = this.antecedent.map (_.formula)
      val ts = this.succedent.map (_.formula)
      val oa = o.antecedent.map (_.formula)
      val os = o.succedent.map (_.formula)

      oa.diff(ta).isEmpty &&  os.diff(ts).isEmpty &&  ta.diff(oa).isEmpty && ts.diff(os).isEmpty
    }

    def syntacticMultisetEquals(o: FSequent ) = {
      val ta = this.antecedent.map (_.formula)
      val ts = this.succedent.map (_.formula)
      val oa = o._1
      val os = o._2

      oa.diff(ta).isEmpty &&  os.diff(ts).isEmpty &&  ta.diff(oa).isEmpty && ts.diff(os).isEmpty
    }

   def =^(o: Sequent): Boolean = syntacticMultisetEquals(o)
   def removeFormulasAtOccurrences(occs: Seq[Occurrence]): Sequent = Sequent(
        antecedent.filterNot(x => occs.contains(x)),
        succedent.filterNot(x => occs.contains(x))
      )
    def getChildOf(fo: Occurrence): Option[FormulaOccurrence] = (antecedent ++ succedent).find(_.ancestors.contains(fo))
    //override def toString : String = antecedent.toString + " :- " + succedent.toString
    def toStringSimple : String = antecedent.foldRight("")( (f, str) => str + ", " + f.formula.toStringSimple ) + " :- " +
                                  succedent.foldRight("")( (f, str) => str + ", " + f.formula.toStringSimple )
    def toFSequent() : FSequent = {
      FSequent(antecedent.map(fo => fo.formula), succedent.map(fo => fo.formula))
    }
    def toFormula = Or( antecedent.toList.map( f => Neg( f.formula ) ) ++ succedent.map(_.formula) )
    // checks whether this sequent is of the form F :- F
    def isTaut = antecedent.size == 1 && succedent.size == 1 && antecedent.head.formula == succedent.head.formula

    def occurrences = antecedent ++ succedent

    //sanity checks for free and bound variables
    // TODO: should this be here??
    def checkFormulaOccurrences(l : Seq[FormulaOccurrence]) = {
      (l filterNot ((fo : FormulaOccurrence) => 
        checkFormulas( List(fo.formula) ++ fo.ancestors.map(((occ:FormulaOccurrence) => occ.formula) ) ))
      ).isEmpty
    }
    
    def checkFormulas(l : Seq[HOLFormula]) = {
      (l.foldLeft(List[LambdaExpression]())((x:List[LambdaExpression], y:HOLFormula) => 
        x ++ checkLambdaExpression(y) )
      ).isEmpty
    }

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
    def getDescendantInLowerSequent(fo: Occurrence): Option[FormulaOccurrence] = {
      (root.antecedent ++ root.succedent).filter(x => x.ancestors.find(y => y == fo) != None) match {
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
    def apply(set: Seq[FormulaOccurrence]): Seq[FormulaOccurrence] = 
    set.map(x =>
    x.factory.createFormulaOccurrence(x.formula.asInstanceOf[HOLFormula], x::Nil))
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

            sb.append(f.formula)
        }
        sb.append(" :- ")
        first =true
        for (f <- s.succedent) {
            if (! first) sb.append(", ")
            else first = false
            sb.append(f.formula)

        }
        sb.toString
    }

    // formats a sequent to a readable string
    def fsequentToString(s : FSequent) : String = {
      var sb = new scala.StringBuilder()
      var first = true
      for (f <- s.antecedent) {
        if (! first) sb.append(", ")
        else first = false

        sb.append(f)
      }
      sb.append(" :- ")
      first =true
      for (f <- s.succedent) {
        if (! first) sb.append(", ")
        else first = false
        sb.append(f)

      }
      sb.toString
    }
  }
}
