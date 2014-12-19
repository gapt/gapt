package at.logic.calculi.lk.base

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.trees._

/**
 * A sequent Γ :- Δ of formulas.
 *
 * @param antecedent The formulas on the left side of the sequent.
 * @param succedent The formulas on the right side of the sequent.
 */
class FSequent(val antecedent : Seq[HOLFormula], val succedent : Seq[HOLFormula]) {
  val _1 = antecedent
  val _2 = succedent

  /**
   * Equality treating each side of the sequent as list, i.e. respecting order and multiplicity.
   */
  override def equals(fs : Any) : Boolean = fs match {
    case FSequent(ant, succ) => (this.antecedent equals ant) && (this.succedent equals succ)
    case _ => false
  }

  override def hashCode: Int = 31 * antecedent.hashCode() + succedent.hashCode()

  override def toString : String =
    this.antecedent.mkString(",") + " :- " + this.succedent.mkString(",")

  /**
   * Equality treating each side of the sequent as a set.
   */
  def setEquals(o: FSequent) = Set(_1) == Set(o._1) && Set(_2) == Set(o._2)

  /**
   * Equality treating each side of the sequent as a multiset.
   */
  def multiSetEquals(o: FSequent) =
    _1.diff(o._1).isEmpty && _2.diff(o._2).isEmpty &&
      o._1.diff(_1).isEmpty && o._2.diff(_2).isEmpty

  /**
   * The formula on both sides of the sequent, i.e. the concatenation of antecedent and succedent.
   */
  def formulas : Seq[HOLFormula] = antecedent ++ succedent

  /**
   * Takes the multiset difference between two sequents, i.e. each side separately.
   */
  def diff(other : FSequent) = FSequent(this.antecedent diff other.antecedent, this.succedent diff other.succedent)

  /**
   * Composes two sequents by taking the concatenation of the formulas on the left side, and on the right side.
   */
  def compose(other: FSequent) = FSequent(antecedent ++ other.antecedent, succedent ++ other.succedent)

  /**
   * Interpretation of the sequent as a formula.
   */
  def toFormula : HOLFormula = Or( antecedent.toList.map( f => Neg( f ) ) ++ succedent )

  /**
   * Are both sides of the sequent empty?
   */
  def isEmpty = _1.isEmpty && _2.isEmpty

  /**
   * Sorts each side of the sequent by [[HOLOrdering]].
   * 
   * @return A copy of this sequent where the two sides are sorted.
   */
  def sorted = FSequent(_1.sorted(HOLOrdering), _2.sorted(HOLOrdering))

  /** Computes the intersection of two sequents.
   *
   * @param other
   * @return
   */
  def intersect(other: FSequent) = FSequent(antecedent intersect other.antecedent, succedent intersect other.succedent)

  /** Computes the union of two sequents.
   *
   * @param other
   * @return
   */
  def union(other: FSequent) = FSequent(antecedent union other.antecedent, succedent union other.succedent)

  /** Removes duplicate formulas from both cedents.
   *
   * @return
   */
  def distinct = FSequent(antecedent.distinct, succedent.distinct)

  /**
   *
   * @param other Another FSequent
   * @return True iff this contains other as a pair of multisets.
   */
  def superMultiSet(other: FSequent) = other subMultiSet this

  /**
   *
   * @param other Another FSequent.
   * @return True iff this contains other as a pair of sets.
   */
  def superSet(other:FSequent) = other subSet this

  def subMultiSet(other: FSequent) = (this diff other).isEmpty

  def subSet(other: FSequent) = (this.distinct diff other.distinct).isEmpty

  /**
   *
   * @return The sequent in tuple form.
   */
  def toTuple = (antecedent, succedent)
}

object FSequent {
  def apply(ant: Seq[HOLFormula], succ: Seq[HOLFormula]) : FSequent =  new FSequent(ant,succ)

  /**
   * Constructs an [[FSequent]] from a [[Sequent]], by ignoring where the formulas occur.
   */
  def apply(seq : Sequent) : FSequent = FSequent(seq.antecedent map (_.formula), seq.succedent map (_.formula))

  /**
   * Destructs an [[FSequent]] into a tuple of its antecedent and succedent.
   */
  def unapply(f: FSequent) : Option[(Seq[HOLFormula], Seq[HOLFormula])] = Some( (f.antecedent, f.succedent) )
}

object FSequentOrdering extends FSequentOrdering

/**
 * Ordering for sequents.
 */
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


/**
 * Sequent of formulas tracking their occurrences in a proof.  Each formula together with its occurrence in a proof is
 * stored as a [[at.logic.calculi.occurrences.FormulaOccurrence]].
 *
 * @param antecedent  The formulas on the left side.
 * @param succedent  The formulas on the right side.
 */
class Sequent(val antecedent: Seq[FormulaOccurrence], val succedent: Seq[FormulaOccurrence]) {
  /**
   * Equality treating each side as a multiset of formulas, ignoring the occurrence.
   */
  def syntacticMultisetEquals(o: Sequent) = FSequent(this) multiSetEquals FSequent(o)

  /**
   * Equality treating each side as a multiset of formulas, ignoring the occurrence.
   */
  def syntacticMultisetEquals(o: FSequent) = FSequent(this) multiSetEquals o

  /**
   * Equality treating each side as a multiset of formulas, ignoring the occurrence.
   */
  def =^(o: Sequent): Boolean = syntacticMultisetEquals(o)
  
  /**
   * Removes the specified [[at.logic.calculi.occurrences.FormulaOccurrence]]s from each side.
   */
  def removeFormulasAtOccurrences(occs: Seq[FormulaOccurrence]): Sequent = Sequent(
    antecedent.filterNot(x => occs.contains(x)),
    succedent.filterNot(x => occs.contains(x))
  )

  /**
   * Finds the first occurrence in this sequent having the given ancestor.
   */
  def getChildOf(ancestor: FormulaOccurrence): Option[FormulaOccurrence] = (antecedent ++ succedent).find(_.parents.contains(ancestor))

  /**
   * Converts to an [[FSequent]], ignoring where the formulas occur.
   */
  def toFSequent: FSequent = FSequent(this)

  /**
   * Interpretation of the sequent as formula.
   */
  def toFormula = toFSequent toFormula

  /**
   * Is this sequent of the form F :- F?
   */
  def isTaut = antecedent.size == 1 && succedent.size == 1 && antecedent.head.formula == succedent.head.formula

  /**
   * Occurrences on both sides of the sequent, i.e. the concatenation of antecedent and succedent.
   */
  def occurrences = antecedent ++ succedent

  /**
   * Is this sequent of the form :- t = t?
   */
  def isReflexivity = antecedent.size == 0 && succedent.size == 1 && (
    succedent.head.formula match {
      case Equation( s, t ) => ( s == t )
      case _ => false
    }
    )

  /**
   * Composes with the other sequent.  The result is the concatenation of the two antecedents as antecedent, and the
   * two succedents as succedent.
   */
  def compose(that : Sequent) = Sequent(this.antecedent ++ that.antecedent, this.succedent ++ that.antecedent)

  override def toString: String = toFSequent toString
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
  override def getMessage = "Could not create lk rule "+name+" from parent "+parent.root+" with auxiliary formulas "+aux.mkString(", ")
}
case class LKBinaryRuleCreationException(name: String, parent1: LKProof, aux1 : HOLFormula,  parent2: LKProof, aux2 : HOLFormula)
  extends LKRuleCreationException("") {
  override def getMessage = "Could not create lk rule "+name+" from left parent "+parent1.root+" with auxiliary formula "+aux1+
    " and right parent "+parent2.root+" with auxiliary formula "+aux2
}

class FormulaNotExistsException(msg: String) extends LKRuleException(msg)

trait LKProof extends TreeProof[Sequent] with Tree[Sequent] {
  def getDescendantInLowerSequent(fo: FormulaOccurrence): Option[FormulaOccurrence] = {
    (root.antecedent ++ root.succedent).filter(_.isDescendantOf(fo, reflexive = true)) match {
      case x :: Nil => Some(x)
      case Nil => None
      case _ => throw new LKRuleException("Illegal lower sequent in rule in application of getDescendantInLowerSequent: More than one such formula exists")
    }
  }

  def containsDescendantOf(fo: FormulaOccurrence): Boolean = getDescendantInLowerSequent(fo) match {
    case Some(_) => true
    case None => false
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

trait TermPositions {
  def termPos: List[HOLPosition]
}

// method for creating the context of the lower sequent. Essentially creating nre occurrences
// create new formula occurrences in the new context
object createContext {
  def apply(set: Seq[FormulaOccurrence]): Seq[FormulaOccurrence] =
    set.map(x =>
      x.factory.createFormulaOccurrence(x.formula.asInstanceOf[HOLFormula], x::Nil))
}


