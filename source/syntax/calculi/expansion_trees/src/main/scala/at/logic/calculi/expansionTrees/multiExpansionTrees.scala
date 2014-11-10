
package at.logic.calculi.expansionTrees

import at.logic.language.hol.{And => AndHOL, Or => OrHOL, Imp => ImpHOL, Neg => NegHOL, _}
import at.logic.utils.ds.trees._
import at.logic.calculi.lk.base.FSequent
import Utility._

/**
 * These trees are the same as expansion trees but consider sequential quantifiers of the same type as quantification over a vector of
 * variables. I.e. an expansion tree having two strong quantifiers over x and y will have a StrongQuantifer child over x and a Strong
 * Quantifier grandchild over y while a multi expansion tree over the same formula will have only StrongQuantifier child over the vector
 * <x,y>
 */

object Utility {
  type T1 = NonTerminalNodeA[Option[HOLFormula],Option[Seq[HOLExpression]]]
  type Instance = (MultiExpansionTree, Seq[HOLExpression])

  /** If formula starts with ∃x,,1,,…∃x,,n,,, returns [x,,1,,,…,x,,n,,]. Otherwise returns Nil.
    *
    * @param formula The formula under consideration.
    * @return
    */
  def getVarsEx(formula: HOLFormula): List[HOLVar] = formula match {
    case ExVar(v,f) => v +: getVarsEx(f)
    case _ => Nil
  }

  /** If formula starts with ∀x,,1,,…∀x,,n,,, returns [x,,1,,,…,x,,n,,]. Otherwise returns Nil.
    *
    * @param formula The formula under consideration.
    * @return
    */
  def getVarsAll(formula: HOLFormula): List[HOLVar] = formula match {
    case AllVar(v,f) => v +: getVarsAll(f)
    case _ => Nil
  }

  /** Strips off the first n quantifiers of a formula.
    * It's only well-defined for formulas that begin with at least n quantifiers.
    *
    * @param formula A HOLFormula
    * @param n Number of quantifiers to be removed
    * @return form without the first n quantifiers
    */
  def removeQuantifiers(formula: HOLFormula, n: Int): HOLFormula =
    if (n == 0)
      formula
    else formula match {
      case AllVar(_,f) => removeQuantifiers(f, n-1)
      case ExVar(_,f) => removeQuantifiers(f, n-1)
      case _ => throw new Exception("Trying to remove too many quantifiers!")
    }
}

trait MultiExpansionTree extends TreeA[Option[HOLFormula],Option[Seq[HOLExpression]]] {

  /** Computes the expansion tree's deep formula.
    *
    * @param pol Determines whether the tree is negated (<0) or not (>0).
    * @return The deep formula.
    */
  def toDeep(pol: Int): HOLFormula

  /**Computes the expansion tree's shallow formula.
    *
    * @return The shallow formula.
    */
  def toShallow: HOLFormula

  /** Tests whether the tree contains any weak quantifier nodes.
    *
    * @return True iff there are weak quantifiers anywhere in the tree.
    */
  def containsWeakQuantifiers: Boolean

  /** Computes the number of instances in an expansion tree. 
    *
    * @return The number of instances in the tree.
    */
  def numberOfInstances: Int

  /** Gets the list of variables instantiated by this node.
    * It will be empty for non-quantifier nodes.
    *
    * @return
    */
  def getVars: List[HOLVar]

  /** Returns a node's shallow formula minus the quantifiers represented by that node.
    *
    * @return The shallow formula of this node minus the quantifiers represented by it (if any).
    */
  def getSubformula: HOLFormula

  /** Returns the number of quantifiers represented by a node.
    *
    * @return The number of quantifiers represented by this node.
    */
  def numberOfQuantifiers: Int
}

/** Models a block of weak quantifiers.
  *
  * Qx,,1,, … Qx,,n,, F +^'''t''',,1,,^ E,,1,, … +^'''t''',,n,,^ E,,n,,
  * @param formula The formula expanded by this tree.
  * @param instances The instance blocks used for the weak quantifiers.
  */
case class MWeakQuantifier(formula: HOLFormula, instances: Seq[Instance])
  extends MultiExpansionTree with T1 {
  lazy val node = Some(formula)
  lazy val children = instances.map(x => (x._1,Some(x._2)))

  override def toDeep(pol: Int): HOLFormula = {
    if (pol > 0)
      OrHOL( instances.map( t => t._1.toDeep(pol)).toList )
    else
      AndHOL(instances.map( t => t._1.toDeep(pol)).toList )
  }
  override def toShallow = formula

  override def containsWeakQuantifiers = true

  override def numberOfInstances = instances.foldLeft(0)((acc, inst) => acc + inst._1.numberOfInstances)

  override def getVars = formula match {
    case ExVar(v, subF) => v +: getVarsEx(subF)
    case AllVar(v, subF) => v +: getVarsAll(subF)
  }

  override def getSubformula = {
    val n = numberOfQuantifiers
    removeQuantifiers(formula, n)
  }

  override def numberOfQuantifiers = instances.head._2.length
}

/** Models a block of strong quantifiers.
  *
  * Qx,,1,, … Qx,,n,, F +^'''α'''^ E
  * @param formula The formula expanded by this tree.
  * @param variables The vector '''α''' of eigenvariables used for the quantifiers.
  * @param selection The expansion tree E.
  */
case class MStrongQuantifier(formula: HOLFormula, variables: Seq[HOLVar], selection: MultiExpansionTree)
  extends MultiExpansionTree with T1 {
  lazy val node = Some(formula)
  lazy val children = List((selection, Some(variables)))

  override def toDeep(pol: Int): HOLFormula = selection.toDeep(pol)
  override def toShallow = formula

  override def containsWeakQuantifiers = selection.containsWeakQuantifiers

  override def numberOfInstances = selection.numberOfInstances

  override def getVars = formula match {
    case ExVar(v, subF) => v +: getVarsEx(subF)
    case AllVar(v, subF) => v +: getVarsAll(subF)
  }

  override def getSubformula = {
    val n = numberOfQuantifiers
    removeQuantifiers(formula, n)
  }

  override def numberOfQuantifiers = variables.length
}
/** Models a block of Skolem quantifiers.
  *
  * Qx,,1,, … Qx,,n,, F +^'''c'''^ E
  * @param formula The formula expanded by this tree.
  * @param skolemSymbols The vector '''c''' of skolem symbols used for the quantifiers.
  * @param selection The expansion tree E.
  */
case class MSkolemQuantifier(formula: HOLFormula, skolemSymbols: Seq[HOLExpression], selection: MultiExpansionTree)
  extends MultiExpansionTree with T1 {
  lazy val node = Some(formula)
  lazy val children = List((selection, Some(skolemSymbols)))

  override def toDeep(pol: Int): HOLFormula = selection.toDeep(pol)
  override def toShallow = formula
  override def containsWeakQuantifiers = selection.containsWeakQuantifiers

  override def numberOfInstances = selection.numberOfInstances

  override def getVars = formula match {
    case ExVar(v, subF) => v +: getVarsEx(subF)
    case AllVar(v, subF) => v +: getVarsAll(subF)
  }

  override def getSubformula = {
    val n = numberOfQuantifiers
    removeQuantifiers(formula, n)
  }

  override def numberOfQuantifiers = skolemSymbols.length
}

/** Models a conjunction.
  *
  *  E,,1,, ∧ E,,2,,
  * @param left The tree E,,1,,.
  * @param right The tree E,,2,,.
  */
case class MAnd(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(left,None),Tuple2(right,None))

  override def toDeep(pol: Int): HOLFormula = AndHOL(left.toDeep(pol), right.toDeep(pol))
  override def toShallow = AndHOL(left.toShallow, right.toShallow)

  override def containsWeakQuantifiers = left.containsWeakQuantifiers || right.containsWeakQuantifiers

  override def numberOfInstances =
    if (!this.containsWeakQuantifiers)
      1
    else
      left.numberOfInstances + right.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}

/** Models a disjunction.
  *
  * E,,1,, ∨ E,,2,,
  * @param left The tree E,,1,,.
  * @param right The tree E,,2,,.
  */
case class MOr(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(left,None),Tuple2(right,None))
  override def toDeep(pol: Int): HOLFormula = OrHOL(left.toDeep(pol), right.toDeep(pol))
  override def toShallow = OrHOL(left.toShallow, right.toShallow)

  override def containsWeakQuantifiers = left.containsWeakQuantifiers || right.containsWeakQuantifiers

  override def numberOfInstances =
    if (!this.containsWeakQuantifiers)
      1
    else
      left.numberOfInstances + right.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}
/** Models an implication.
  *
  * E,,1,, → E,,2,,
  * @param left The tree E,,1,,.
  * @param right The tree E,,2,,.
  */
case class MImp(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(left,None),Tuple2(right,None))
  override def toDeep(pol: Int): HOLFormula = ImpHOL(left.toDeep(-pol), right.toDeep(pol))
  override def toShallow = ImpHOL(left.toShallow, right.toShallow)

  override def containsWeakQuantifiers = left.containsWeakQuantifiers || right.containsWeakQuantifiers

  override def numberOfInstances =
    if (!this.containsWeakQuantifiers)
      1
    else
      left.numberOfInstances + right.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}

/** Models a negation.
  *
  * ¬ E
  * @param tree The tree E.
  */
case class MNeg(tree: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(tree,None))
  override def toDeep(pol: Int): HOLFormula = NegHOL(tree.toDeep(-pol))
  override def toShallow = NegHOL(tree.toShallow)

  override def containsWeakQuantifiers = tree.containsWeakQuantifiers

  override def numberOfInstances =
    if (!this.containsWeakQuantifiers)
      1
    else
      tree.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}

/** Models an atomic expansion tree.
  *
  * Atom(f)
  * @param formula The formula f.
  */
case class MAtom(formula: HOLFormula) extends MultiExpansionTree with TerminalNodeA[Option[HOLFormula],Option[Seq[HOLExpression]]] {
  lazy val node = Some(formula)
  override def toDeep(pol: Int): HOLFormula = formula
  override def toShallow = formula

  override def containsWeakQuantifiers = false

  override def numberOfInstances = 1

  override def getVars = Nil

  override def getSubformula = formula

  override def numberOfQuantifiers = 0
}

/** Implements sequents of MultiExpansionTrees, analogous to [[at.logic.calculi.expansionTrees.ExpansionSequent]]s.
  *
  * @param antecedent The antecedent of the sequent.
  * @param succedent The succedent of the sequent.
  */
class MultiExpansionSequent(val antecedent: Seq[MultiExpansionTree], val succedent: Seq[MultiExpansionTree]) {
  def toTuple: (Seq[MultiExpansionTree], Seq[MultiExpansionTree]) = {
    (antecedent, succedent)
  }

  /** Maps a function over the sequent.
    *
    * @param f A function of type [[at.logic.calculi.expansionTrees.MultiExpansionTree]] → [[at.logic.calculi.expansionTrees.MultiExpansionTree]]
    * @return The result of the map.
    */
  def map(f : MultiExpansionTree => MultiExpansionTree): MultiExpansionSequent = {
    new MultiExpansionSequent(antecedent.map(f), succedent.map(f))
  }

  /** Maps a function over the sequent.
    *
    * @param f A function of type [[at.logic.calculi.expansionTrees.MultiExpansionTree]] → [[at.logic.language.hol.HOLFormula]]
    * @return The result of the map.
    */
  def map(f: MultiExpansionTree => HOLFormula): FSequent = {
    new FSequent(antecedent.map(f), succedent.map(f))
  }

  /** Adds an expansion tree to the antecedent of the sequent.
    *
    * @param et The expansion tree to be added.
    * @return The extended sequent.
    */
  def addToAntecedent(et: MultiExpansionTree): MultiExpansionSequent = {
    new MultiExpansionSequent(et +: antecedent, succedent)
  }

  /** Adds an expansion tree to the succedent of the sequent.
    *
    * @param et The expansion tree to be added.
    * @return The extended sequent.
    */
  def addToSuccedent(et: MultiExpansionTree): MultiExpansionSequent = {
    new MultiExpansionSequent(antecedent, et +: succedent)
  }

  /** Removes an expansion tree from the antecedent of the sequent.
    *
    * @param et The expansion tree to be removed.
    * @return The reduced sequent.
    */
  def removeFromAntecedent(et: MultiExpansionTree): MultiExpansionSequent = {
    require(antecedent.exists(_ eq et))
    new MultiExpansionSequent(antecedent.filterNot(_ eq et), succedent)
  }

  /** Removes an expansion tree from the succedent of the sequent.
    *
    * @param et The expansion tree to be removed.
    * @return The reduced sequent.
    */
  def removeFromSuccedent(et: MultiExpansionTree): MultiExpansionSequent = {
    require(succedent.exists(_ eq et))
    new MultiExpansionSequent(antecedent, succedent.filterNot(_ eq et))
  }

  /** Replaces an expansion in the antecedent.
    *
    * @param from The expansion tree to be replaced.
    * @param to The replacement tree.
    * @return The modified sequent.
    */
  def replaceInAntecedent(from: MultiExpansionTree, to: MultiExpansionTree): MultiExpansionSequent = {
    require(antecedent.exists(_ eq from))
    new MultiExpansionSequent(antecedent.map(et => if (et eq from) to else et), succedent)
  }

  /** Replaces an expansion in the succedent.
    *
    * @param from The expansion tree to be replaced.
    * @param to The replacement tree.
    * @return The modified sequent.
    */
  def replaceInSuccedent(from: MultiExpansionTree, to: MultiExpansionTree): MultiExpansionSequent = {
    require(succedent.exists(_ eq from))
    new MultiExpansionSequent(antecedent, succedent.map(et => if (et eq from) to else et))
  }

  override def toString: String = "MultiExpansionSequent("+antecedent+", "+succedent+")"

  def canEqual(other: Any): Boolean = other.isInstanceOf[MultiExpansionSequent]

  override def equals(other: Any): Boolean = other match {
    case that: MultiExpansionSequent =>
      (that canEqual this) &&
        antecedent == that.antecedent &&
        succedent == that.succedent
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(antecedent, succedent)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }

  def toShallow = map((t: MultiExpansionTree) => t.toShallow)
  def toDeep : FSequent = {
    val newAnt = antecedent.map(t => t.toDeep(-1))
    val newSuc = succedent.map(t => t.toDeep(1))

    FSequent(newAnt, newSuc)
  }
}
object MultiExpansionSequent {
  def apply(antecedent: Seq[MultiExpansionTree], succedent: Seq[MultiExpansionTree]) = new MultiExpansionSequent(antecedent, succedent)
  def unapply(etSeq: MultiExpansionSequent) = Some( etSeq.toTuple )
}



