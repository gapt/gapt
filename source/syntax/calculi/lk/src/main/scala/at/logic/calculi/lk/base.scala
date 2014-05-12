/*
 * base.scala
 *
 */

package at.logic.calculi.lk.base

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.trees._
import at.logic.utils.traits.Occurrence
import at.logic.utils.dssupport.ListSupport.lst2string

class FSequent(val antecedent : Seq[HOLFormula], val succedent : Seq[HOLFormula]) {
  val _1 = antecedent
  val _2 = succedent

  override def equals(fs : Any) : Boolean = fs match {
    case FSequent(ant, succ) => (this.antecedent equals ant) && (this.succedent equals succ)
    case _ => false
  }

  // formats a sequent to a readable string
  override def toString : String =
    lst2string(((x: HOLFormula) => x.toString), ", ", this.antecedent.toList) + " :- " + lst2string(((x: HOLFormula) => x.toString), ", ", this.succedent.toList)

  def setEquals(g:FSequent) = FSequent.setEquals(this, g)
  def multiSetEquals(g:FSequent) = FSequent.multiSetEquals(this, g)
  def formulas : Seq[HOLFormula] = antecedent ++ succedent

  def diff(that : FSequent) = FSequent(this.antecedent diff that.antecedent, this.succedent diff that.succedent)

  /*
   compose constructs a sequent from two sequents. Corresponds to the 'o' operator in CERes
  */
  def compose(other: FSequent) = FSequent(antecedent ++ other.antecedent, succedent ++ other.succedent)

  def toFormula : HOLFormula = Or( antecedent.toList.map( f => Neg( f ) ) ++ succedent )

  def isEmpty = _1.isEmpty && _2.isEmpty

  def sorted = FSequent(_1.sorted(HOLOrdering), _2.sorted(HOLOrdering))

}

object FSequent {
  def apply(ant: Seq[HOLFormula], succ: Seq[HOLFormula]) : FSequent =  new FSequent(ant,succ)
  def apply(seq : Sequent) : FSequent = FSequent(seq.antecedent map (_.formula), seq.succedent map (_.formula))

  def unapply(f: FSequent) : Option[(Seq[HOLFormula], Seq[HOLFormula])] = Some( (f.antecedent, f.succedent) )

  def setEquals(f: FSequent, g: FSequent) : Boolean =
    Set(f._1) == Set(g._1) &&
      Set(f._2) == Set(g._2)

  def multiSetEquals(f : FSequent, g : FSequent) : Boolean =
    f._1.diff(g._1).isEmpty && f._2.diff(g._2).isEmpty &&
      g._1.diff(f._1).isEmpty && g._2.diff(f._2).isEmpty


  /*
   compose constructs a sequent from two sequents. Corresponds to the 'o' operator in CERes
  */
}

object FSequentOrdering extends FSequentOrdering;
class FSequentOrdering extends Ordering[FSequent]  {
  def compare(x:FSequent,y:FSequent)  : Int = {
    if (x.antecedent.size < y.antecedent.size) -1 else
    if (y.antecedent.size < x.antecedent.size) 1 else
    if (x.antecedent.size == y.antecedent.size && x.succedent.size < y.succedent.size) -1 else
    if (x.antecedent.size == y.antecedent.size && y.succedent.size < x.succedent.size) 1 else
    {
      assert(x.antecedent.size == y.antecedent.size &&
        x.succedent.size == y.succedent.size, "Implementation error comparing FSequents!")
      val xs = x.sorted.formulas
      val ys = y.sorted.formulas
      val xys = xs zip ys
      xys.foldLeft(0)( (rv, pair) => {
        //as long as it is undecided, we compare pairs
        if (rv == 0) HOLOrdering.compare(pair._1, pair._2)
        //otherwise we pass the result on
        else rv
      })
    }
  }
}



class Sequent(val antecedent: Seq[FormulaOccurrence], val succedent: Seq[FormulaOccurrence]) {

  //TODO improve both equals methods
  def multisetEquals( o: Sequent ) = o.antecedent.diff(antecedent).isEmpty &&
    o.succedent.diff(succedent).isEmpty &&
    antecedent.diff(o.antecedent).isEmpty &&
    succedent.diff(o.succedent).isEmpty
  def setEquals(o: Sequent ) = antecedent.forall(a => o.antecedent.contains(a)) &&
    succedent.forall(a => o.succedent.contains(a)) &&
    o.antecedent.forall(a => antecedent.contains(a)) &&
    o.succedent.forall(a => succedent.contains(a))
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

  def toFSequent() : FSequent = {
    FSequent(antecedent.map(fo => fo.formula), succedent.map(fo => fo.formula))
  }

  def toFormula = Or( antecedent.toList.map( f => Neg( f.formula ) ) ++ succedent.map(_.formula) )

  // checks whether this sequent is of the form F :- F
  def isTaut = antecedent.size == 1 && succedent.size == 1 && antecedent.head.formula == succedent.head.formula

  def occurrences = antecedent ++ succedent

  // checks whether this sequent is of the form :- t = t
  def isReflexivity = antecedent.size == 0 && succedent.size == 1 && (
    succedent.head.formula match {
      case Equation( s, t ) => ( s == t )
      case _ => false
    }
    )

  // formats a sequent to a readable string
  // TODO: this can be done in a more functional way.
  override def toString : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- this.antecedent) {
      if (!first) sb.append(", ")
      else first = false
      sb.append(f.formula)
    }
    sb.append(" :- ")
    first = true
    for (f <- this.succedent) {
      if (!first) sb.append(", ")
      else first = false
      sb.append(f.formula)
    }
    sb.toString
  }




}

object Sequent {
  def apply(antecedent: Seq[FormulaOccurrence], succedent: Seq[FormulaOccurrence]) = new Sequent(antecedent, succedent)
  def unapply(so: Sequent) = Some(so.antecedent, so.succedent)
}

// exceptions
class LKRuleException(msg: String) extends RuleException(msg)
class LKRuleCreationException(msg: String) extends LKRuleException(msg)
//these two classes allow detailed error diagnosis
case class LKUnaryRuleCreationException(name: String, parent: LKProof, aux : List[HOLFormula])
  extends LKRuleCreationException("") {
  override def getMessage() = "Could not create lk rule "+name+" from parent "+parent.root+" with auxiliary formulas "+aux.mkString(", ")
}
case class LKBinaryRuleCreationException(name: String, parent1: LKProof, aux1 : HOLFormula,  parent2: LKProof, aux2 : HOLFormula)
  extends LKRuleCreationException("") {
  override def getMessage() = "Could not create lk rule "+name+" from left parent "+parent1.root+" with auxiliary formula "+aux1+
    " and right parent "+parent2.root+" with auxiliary formula "+aux2
}

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


