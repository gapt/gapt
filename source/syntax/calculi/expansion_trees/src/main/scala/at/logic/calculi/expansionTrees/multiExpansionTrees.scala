
package at.logic.calculi.expansionTrees

import at.logic.language.hol.{And => AndHOL, Or => OrHOL, Imp => ImpHOL, Neg => NegHOL, _}
import at.logic.utils.ds.trees._
import at.logic.calculi.lk.base.FSequent

/**
 * These trees are the same as expansion trees but consider sequential quantifiers of the same type as quantification over a vector of
 * variables. I.e. an expansion tree having two strong quantifiers over x and y will have a StrongQuantifer child over x and a Strong
 * Quantifier grandchild over y while a multi expansion tree over the same formula will have only StrongQuantifier child over the vector
 * <x,y>
 */
object multi {

type T1 = NonTerminalNodeA[Option[HOLFormula],Option[Seq[HOLExpression]]]

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
}

  /** Models a block of weak quantifiers.
   * Qx,,1,, … Qx,,n,, F +^''t'',,1,,^ E_1 … +^''t'',,n,,^ E_n
   * @param formula The formula expanded by this tree.
   * @param instances The instance blocks used for the weak quantifiers.
   */
case class WeakQuantifier(formula: HOLFormula, instances: Seq[Tuple2[MultiExpansionTree, Seq[HOLExpression]]])
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
}

  /** Models a block of strong quantifiers.
   * Qx,,1,, … Qx,,n,, F +^''α''^ E
   * @param formula The formula expanded by this tree.
   * @param variables The vector ''α'' of eigenvariables used for the quantifiers.
   * @param selection The expansion tree E.
   */
case class StrongQuantifier(formula: HOLFormula, variables: Seq[HOLVar], selection: MultiExpansionTree)
  extends MultiExpansionTree with T1 {
  lazy val node = Some(formula)
  lazy val children = List((selection, Some(variables)))

  override def toDeep(pol: Int): HOLFormula = selection.toDeep(pol)
  override def toShallow = formula
}
  /** Models a block of symbol quantifiers.
   * Qx,,1,, … Qx,,n,, F +^''c''^ E
  * @param formula The formula expanded by this tree.
  * @param skolem_constants The vector ''c'' of skolem symbols used for the quantifiers.
  * @param selection The expansion tree E.
  */
case class SkolemQuantifier(formula: HOLFormula, skolem_constants: Seq[HOLExpression], selection: MultiExpansionTree)
    extends MultiExpansionTree with T1 {
    lazy val node = Some(formula)
    lazy val children = List((selection, Some(skolem_constants)))

    override def toDeep(pol: Int): HOLFormula = selection.toDeep(pol)
    override def toShallow = formula
}

  /** Models a conjunction.
   *  E,,1,, ∧ E,,2,,
   * @param left The tree E,,1,,.
   * @param right The tree E,,2,,.
   */
case class And(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(left,None),Tuple2(right,None))

  override def toDeep(pol: Int): HOLFormula = AndHOL(left.toDeep(pol), right.toDeep(pol))
  override def toShallow = AndHOL(left.toShallow, right.toShallow)
}

  /** Models a disjunction.
   * E,,1,, ∨ E,,2,,
   * @param left The tree E,,1,,.
   * @param right The tree E,,2,,.
   */
case class Or(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(left,None),Tuple2(right,None))
  override def toDeep(pol: Int): HOLFormula = OrHOL(left.toDeep(pol), right.toDeep(pol))
  override def toShallow = OrHOL(left.toShallow, right.toShallow)
}
  /** Models an implication.
    * E,,1,, → E,,2,,
    * @param left The tree E,,1,,.
    * @param right The tree E,,2,,.
    */
case class Imp(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(left,None),Tuple2(right,None))
  override def toDeep(pol: Int): HOLFormula = ImpHOL(left.toDeep(-pol), right.toDeep(pol))
  override def toShallow = ImpHOL(left.toShallow, right.toShallow)
}

  /** Models a negation.
   * ¬ E,,,,
   * @param tree The tree E.
   */
case class Not(tree: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Tuple2(tree,None))
  override def toDeep(pol: Int): HOLFormula = NegHOL(tree.toDeep(-pol))
  override def toShallow = NegHOL(tree.toShallow)
}

  /** Models an atomic expansion tree.
   * Atom(f)
   * @param formula The formula f.
   */
case class Atom(formula: HOLFormula) extends MultiExpansionTree with TerminalNodeA[Option[HOLFormula],Option[Seq[HOLExpression]]] {
  lazy val node = Some(formula)
  override def toDeep(pol: Int): HOLFormula = formula
  override def toShallow = formula
}

// TODO: is there a way to make this and the toFormula method from ExpansionTree
// the same??
// This has to be inside the "multi" object, otherwise the type
// MultiExpansionTree is not recognized.
// Why is this implementation inside an object and the other (ExpansionTree) is
// not?
// Can I call this using the dot notation? (met.toFormulaM)
def toFormulaM(tree: MultiExpansionTree): HOLFormula = tree match {
  case Atom(f) => f
  case Not(t1) => NegHOL(toFormulaM(t1))
  case And(t1,t2) => AndHOL(toFormulaM(t1), toFormulaM(t2))
  case Or(t1,t2) => OrHOL(toFormulaM(t1), toFormulaM(t2))
  case Imp(t1,t2) => ImpHOL(toFormulaM(t1), toFormulaM(t2))
  case WeakQuantifier(f,_) => f
  case StrongQuantifier(f,_,_) => f
  case SkolemQuantifier(f,_,_) => f
}

def quantRulesNumber(tree: MultiExpansionTree): Int = tree match {
  case Atom(f) => 0
  case Not(t1) => quantRulesNumber(t1)
  case And(t1,t2) => quantRulesNumber(t1) + quantRulesNumber(t2)
  case Or(t1,t2) => quantRulesNumber(t1) + quantRulesNumber(t2)
  case Imp(t1,t2) => quantRulesNumber(t1) + quantRulesNumber(t2)
  case WeakQuantifier(_,children) => children.foldRight(0){
    case ((et, _), sum) => quantRulesNumber(et) + 1 + sum
  }
  case StrongQuantifier(_,vars,et) => quantRulesNumber(et) + vars.size
  case SkolemQuantifier(_,cs,et) => quantRulesNumber(et) + cs.size
}

def containsWeakQuantifiers(tree: MultiExpansionTree): Boolean = tree match {
  case Atom(f) => false
  case And(left, right) => containsWeakQuantifiers(left) || containsWeakQuantifiers(right)
  case Or(left, right)  => containsWeakQuantifiers(left) || containsWeakQuantifiers(right)
  case Imp(left, right) => containsWeakQuantifiers(left) || containsWeakQuantifiers(right)
  case Not(s) => containsWeakQuantifiers(s)
  case StrongQuantifier(_,_,sel) => containsWeakQuantifiers(sel)
  case SkolemQuantifier(_,_,sel) => containsWeakQuantifiers(sel)
  case WeakQuantifier(_,_) => true
}

def numberOfInstances(tree: MultiExpansionTree): Int = {
  if(!containsWeakQuantifiers(tree))
    1
  else tree match {
    case And(left, right) => numberOfInstances(left) + numberOfInstances(right)
    case Or(left, right)  => numberOfInstances(left) + numberOfInstances(right)
    case Imp(left, right) => numberOfInstances(left) + numberOfInstances(right)
    case Not(s) => numberOfInstances(s)
    case StrongQuantifier(_,_,sel) => numberOfInstances(sel)
    case SkolemQuantifier(_,_,sel) => numberOfInstances(sel)
    case WeakQuantifier(_,inst) => inst.length
  }
}

  /** Gets the list of variables instantiated by this node.
    * It will be empty for non-quantifier nodes.
   *
   * @param tree The expansion tree under consideration.
   * @return
   */
  def getVars(tree: MultiExpansionTree): List[HOLVar] = tree match {
    case WeakQuantifier(f,_) =>
      f match {
        case ExVar(v, subF) => v +: getVarsEx(subF)
        case AllVar(v, subF) => v +: getVarsAll(subF)
      }
    case StrongQuantifier(f,_,_) =>
      f match {
        case ExVar(v, subF) => v +: getVarsEx(subF)
        case AllVar(v, subF) => v +: getVarsAll(subF)
      }
    case SkolemQuantifier(f,_,_) =>
      f match {
        case ExVar(v, subF) => v +: getVarsEx(subF)
        case AllVar(v, subF) => v +: getVarsAll(subF)
      }
    case _ => Nil
  }

  private def getVarsEx(form: HOLFormula): List[HOLVar] = form match {
    case ExVar(v,f) => v +: getVarsEx(f)
    case _ => Nil
  }

  private def getVarsAll(form: HOLFormula): List[HOLVar] = form match {
    case AllVar(v,f) => v +: getVarsAll(f)
    case _ => Nil
  }

  /** Strips off the first n quantifiers of a formula.
    * It's only well-defined for formulas that begin with at least n quantifiers.
   * 
   * @param form A HOLFormula
   * @param n Number of quantifiers to be removed
   * @return form without the first n quantifiers
   */
  private def removeQuantifiers(form: HOLFormula, n: Int): HOLFormula =
    if (n == 0)
      form
    else form match {
      case AllVar(_,f) => removeQuantifiers(f, n-1)
      case ExVar(_,f) => removeQuantifiers(f, n-1)
  }

  /** Returns a node's shallow formula minus the quantifiers represented by that node.
   *
   * @param et A MultiExpansionTree
   * @return The shallow formula of et minus the quantifiers of et (if any).
   */
  def getSubformula(et: MultiExpansionTree): HOLFormula = et match {
    case WeakQuantifier(_,_) | StrongQuantifier(_,_,_) | SkolemQuantifier(_,_,_)  =>
      val n = numberOFQuantifiers(et)
      val f = et.toShallow
      removeQuantifiers(f,n)
    case _ => et.toShallow
  }

  /** Returns the number of quantifiers represented by a node.
   * 
   * @param et A MultiExpansionTree
   * @return The number of quantifiers represented by et's root
   */
  def numberOFQuantifiers(et: MultiExpansionTree): Int = et match {
    case WeakQuantifier(_, inst) => inst.head._2.length
    case StrongQuantifier(_, vars, _) => vars.length
    case SkolemQuantifier(_, skol, _) => skol.length
    case _ => 0
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
     * @param f A function of type [[at.logic.calculi.expansionTrees.multi.MultiExpansionTree]] → [[at.logic.calculi.expansionTrees.multi.MultiExpansionTree]]
     * @return The result of the map.
     */
  def map(f : MultiExpansionTree => MultiExpansionTree): MultiExpansionSequent = {
    new MultiExpansionSequent(antecedent.map(f), succedent.map(f))
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

}



