
package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.utils.ds.trees._
import at.logic.gapt.proofs.lk.base.HOLSequent
import Utility._

/**
 * These trees are the same as expansion trees but consider sequential quantifiers of the same type as quantification over a vector of
 * variables. I.e. an expansion tree having two strong quantifiers over x and y will have a StrongQuantifer child over x and a Strong
 * Quantifier grandchild over y while a multi expansion tree over the same formula will have only StrongQuantifier child over the vector
 * <x,y>
 */

object Utility {
  type T1 = NonTerminalNodeA[Option[HOLFormula], Option[Seq[LambdaExpression]]]
  type Instance = ( MultiExpansionTree, Seq[LambdaExpression] )
}

trait MultiExpansionTree extends TreeA[Option[HOLFormula], Option[Seq[LambdaExpression]]] {

  /**
   * Computes the expansion tree's deep formula.
   *
   * @param pol Determines whether the tree is negated (<0) or not (>0).
   * @return The deep formula.
   */
  def toDeep( pol: Int ): HOLFormula

  /**
   * Computes the expansion tree's shallow formula.
   *
   * @return The shallow formula.
   */
  def toShallow: HOLFormula

  /**
   * Tests whether the tree contains any weak quantifier nodes.
   *
   * @return True iff there are weak quantifiers anywhere in the tree.
   */
  def containsWeakQuantifiers: Boolean

  /**
   * Computes the number of instances in an expansion tree.
   *
   * @return The number of instances in the tree.
   */
  def numberOfInstances: Int

  /**
   * Gets the list of variables instantiated by this node.
   * It will be empty for non-quantifier nodes.
   *
   * @return
   */
  def getVars: List[Var]

  /**
   * Returns a node's shallow formula minus the quantifiers represented by that node.
   *
   * @return The shallow formula of this node minus the quantifiers represented by it (if any).
   */
  def getSubformula: HOLFormula

  /**
   * Returns the number of quantifiers represented by a node.
   *
   * @return The number of quantifiers represented by this node.
   */
  def numberOfQuantifiers: Int
}

/**
 * Models a block of weak quantifiers.
 *
 * Qx,,1,, … Qx,,n,, F +^'''t''',,1,,^ E,,1,, … +^'''t''',,n,,^ E,,n,,
 * @param formula The formula expanded by this tree.
 * @param instances The instance blocks used for the weak quantifiers.
 */
case class METWeakQuantifier( formula: HOLFormula, instances: Seq[Instance] )
    extends MultiExpansionTree with T1 {
  lazy val node = Some( formula )
  lazy val children = instances.map( x => ( x._1, Some( x._2 ) ) )

  override def toDeep( pol: Int ): HOLFormula = {
    if ( pol > 0 )
      Or( instances.map( t => t._1.toDeep( pol ) ).toList )
    else
      And( instances.map( t => t._1.toDeep( pol ) ).toList )
  }
  override def toShallow = formula

  override def containsWeakQuantifiers = true

  override def numberOfInstances = instances.foldLeft( 0 )( ( acc, inst ) => acc + inst._1.numberOfInstances )

  override def getVars = formula match {
    case Ex( v, subF )  => v +: variablesEx( subF )
    case All( v, subF ) => v +: variablesAll( subF )
  }

  override def getSubformula = {
    val n = numberOfQuantifiers
    removeQuantifiers( formula, n )
  }

  override def numberOfQuantifiers = instances.head._2.length
}

/**
 * Models a block of strong quantifiers.
 *
 * Qx,,1,, … Qx,,n,, F +^'''α'''^ E
 * @param formula The formula expanded by this tree.
 * @param variables The vector '''α''' of eigenvariables used for the quantifiers.
 * @param selection The expansion tree E.
 */
case class METStrongQuantifier( formula: HOLFormula, variables: Seq[Var], selection: MultiExpansionTree )
    extends MultiExpansionTree with T1 {
  lazy val node = Some( formula )
  lazy val children = List( ( selection, Some( variables ) ) )

  override def toDeep( pol: Int ): HOLFormula = selection.toDeep( pol )
  override def toShallow = formula

  override def containsWeakQuantifiers = selection.containsWeakQuantifiers

  override def numberOfInstances = selection.numberOfInstances

  override def getVars = formula match {
    case Ex( v, subF )  => v +: variablesEx( subF )
    case All( v, subF ) => v +: variablesAll( subF )
  }

  override def getSubformula = {
    val n = numberOfQuantifiers
    removeQuantifiers( formula, n )
  }

  override def numberOfQuantifiers = variables.length
}

/**
 * Models a block of Skolem quantifiers.
 *
 * Qx,,1,, … Qx,,n,, F +^'''c'''^ E
 * @param formula The formula expanded by this tree.
 * @param skolemSymbols The vector '''c''' of skolem symbols used for the quantifiers.
 * @param selection The expansion tree E.
 */
case class METSkolemQuantifier( formula: HOLFormula, skolemSymbols: Seq[LambdaExpression], selection: MultiExpansionTree )
    extends MultiExpansionTree with T1 {
  lazy val node = Some( formula )
  lazy val children = List( ( selection, Some( skolemSymbols ) ) )

  override def toDeep( pol: Int ): HOLFormula = selection.toDeep( pol )
  override def toShallow = formula
  override def containsWeakQuantifiers = selection.containsWeakQuantifiers

  override def numberOfInstances = selection.numberOfInstances

  override def getVars = formula match {
    case Ex( v, subF )  => v +: variablesEx( subF )
    case All( v, subF ) => v +: variablesAll( subF )
  }

  override def getSubformula = {
    val n = numberOfQuantifiers
    removeQuantifiers( formula, n )
  }

  override def numberOfQuantifiers = skolemSymbols.length
}

/**
 * Models a conjunction.
 *
 *  E,,1,, ∧ E,,2,,
 * @param left The tree E,,1,,.
 * @param right The tree E,,2,,.
 */
case class METAnd( left: MultiExpansionTree, right: MultiExpansionTree ) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List( Tuple2( left, None ), Tuple2( right, None ) )

  override def toDeep( pol: Int ): HOLFormula = And( left.toDeep( pol ), right.toDeep( pol ) )
  override def toShallow = And( left.toShallow, right.toShallow )

  override def containsWeakQuantifiers = left.containsWeakQuantifiers || right.containsWeakQuantifiers

  override def numberOfInstances =
    if ( !this.containsWeakQuantifiers )
      1
    else
      left.numberOfInstances + right.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}

/**
 * Models a disjunction.
 *
 * E,,1,, ∨ E,,2,,
 * @param left The tree E,,1,,.
 * @param right The tree E,,2,,.
 */
case class METOr( left: MultiExpansionTree, right: MultiExpansionTree ) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List( Tuple2( left, None ), Tuple2( right, None ) )
  override def toDeep( pol: Int ): HOLFormula = Or( left.toDeep( pol ), right.toDeep( pol ) )
  override def toShallow = Or( left.toShallow, right.toShallow )

  override def containsWeakQuantifiers = left.containsWeakQuantifiers || right.containsWeakQuantifiers

  override def numberOfInstances =
    if ( !this.containsWeakQuantifiers )
      1
    else
      left.numberOfInstances + right.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}

/**
 * Models an implication.
 *
 * E,,1,, → E,,2,,
 * @param left The tree E,,1,,.
 * @param right The tree E,,2,,.
 */
case class METImp( left: MultiExpansionTree, right: MultiExpansionTree ) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List( Tuple2( left, None ), Tuple2( right, None ) )
  override def toDeep( pol: Int ): HOLFormula = Imp( left.toDeep( -pol ), right.toDeep( pol ) )
  override def toShallow = Imp( left.toShallow, right.toShallow )

  override def containsWeakQuantifiers = left.containsWeakQuantifiers || right.containsWeakQuantifiers

  override def numberOfInstances =
    if ( !this.containsWeakQuantifiers )
      1
    else
      left.numberOfInstances + right.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}

/**
 * Models a negation.
 *
 * ¬ E
 * @param tree The tree E.
 */
case class METNeg( tree: MultiExpansionTree ) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List( Tuple2( tree, None ) )
  override def toDeep( pol: Int ): HOLFormula = Neg( tree.toDeep( -pol ) )
  override def toShallow = Neg( tree.toShallow )

  override def containsWeakQuantifiers = tree.containsWeakQuantifiers

  override def numberOfInstances =
    if ( !this.containsWeakQuantifiers )
      1
    else
      tree.numberOfInstances

  override def getVars = Nil

  override def getSubformula = toShallow

  override def numberOfQuantifiers = 0
}

/**
 * Models an atomic expansion tree.
 *
 * Atom(f)
 * @param atom The formula f.
 */
case class METAtom( atom: HOLAtom ) extends MultiExpansionTree with TerminalNodeA[Option[HOLFormula], Option[Seq[LambdaExpression]]] {
  lazy val node = Some( atom )
  override def toDeep( pol: Int ): HOLFormula = atom
  override def toShallow = atom

  override def containsWeakQuantifiers = false

  override def numberOfInstances = 1

  override def getVars = Nil

  override def getSubformula = atom

  override def numberOfQuantifiers = 0
}

case object METTop extends MultiExpansionTree {
  lazy val node = Some( Top() )
  override def toDeep( pol: Int ) = Top()
  override def toShallow = Top()

  override def containsWeakQuantifiers = false

  override def numberOfInstances = 1

  override def getVars = Nil

  override def getSubformula = Top()

  override def numberOfQuantifiers = 0
}

case object METBottom extends MultiExpansionTree {
  lazy val node = Some( Bottom() )
  override def toDeep( pol: Int ) = Bottom()
  override def toShallow = Bottom()

  override def containsWeakQuantifiers = false

  override def numberOfInstances = 1

  override def getVars = Nil

  override def getSubformula = Bottom()

  override def numberOfQuantifiers = 0
}

/**
 * Models a weakening in an expansion tree.
 */
case class METWeakening( formula: HOLFormula ) extends MultiExpansionTree with TerminalNodeA[Option[HOLFormula], Option[Seq[LambdaExpression]]] {
  lazy val node = Some( formula )
  override def toDeep( pol: Int ): HOLFormula = if ( pol > 0 ) Bottom() else Top()
  override def toShallow = formula

  override def containsWeakQuantifiers = false

  override def numberOfInstances = 1

  override def getVars = Nil

  override def getSubformula = formula

  override def numberOfQuantifiers = 0
}

object MultiExpansionSequent {
  def apply( antecedent: Seq[MultiExpansionTree], succedent: Seq[MultiExpansionTree] ) = new MultiExpansionSequent( antecedent, succedent )
  def unapply( etSeq: MultiExpansionSequent ) = Some( etSeq.toTuple )
}

