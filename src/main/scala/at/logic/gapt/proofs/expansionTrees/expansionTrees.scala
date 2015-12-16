package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ NaiveIncompleteMatchingAlgorithm, containsQuantifier, HOLPosition }
import at.logic.gapt.proofs.lk.solve
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.utils.ds.trees._
import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.collection.immutable.HashMap

/**
 * General class for expansion trees with pseudo case classes including for MergeNodes, which only occur during merging/substituting
 */
trait ExpansionTreeWithMerges extends TreeA[Option[HOLFormula], Option[LambdaExpression]] {
  override def toString = this match {
    case ETTop => "Top"
    case ETBottom => "Bottom"
    case ETAtom( f ) => "Atom(" + f.toString + ")"
    case ETWeakening( f ) => "Weakening(" + f.toString + ")"
    case ETNeg( t1 ) => NegC.name + t1.toString
    case ETAnd( t1, t2 ) => t1.toString + AndC.name + t2.toString
    case ETOr( t1, t2 ) => t1.toString + OrC.name + t2.toString
    case ETImp( t1, t2 ) => t1.toString + ImpC.name + t2.toString
    case ETWeakQuantifier( formula, children ) => "WeakQuantifier(" + formula + ", " + children + ")"
    case ETStrongQuantifier( formula, variable, selection ) => "StrongQuantifier(" + formula + ", " + variable + ", " + selection + ")"
    case ETSkolemQuantifier( formula, sk, selection ) => "SkolemQuantifier(" + formula + ", " + sk + ", " + selection + ")"
    case ETMerge( left, right ) => "MergeNode(" + left + ", " + right + ")"
    case _ => throw new Exception( "Unhandled case in ExpansionTreeWithMerges.toString" )
  }

  private val emptytreemap = HashMap[ExpansionTreeWithMerges, Int]()
  /* number of nodes in tree */
  def size(): Int = size( emptytreemap )( this )
  def size( visited: Map[ExpansionTreeWithMerges, Int] ): Map[ExpansionTreeWithMerges, Int] =
    if ( visited contains this )
      visited
    else this match {
      case ETAtom( _ )      => visited + ( ( this, 1 ) )
      case ETWeakening( _ ) => visited + ( ( this, 1 ) )
      case ETNeg( child ) =>
        val nvisited = child.size( visited )
        nvisited + ( ( this, nvisited( child ) + 1 ) )
      case ETAnd( child1, child2 ) =>
        val nvisited1 = child1.size( visited )
        val nvisited2 = child2.size( nvisited1 )
        nvisited2 + ( ( this, nvisited2( child1 ) + nvisited2( child2 ) + 1 ) )
      case ETOr( child1, child2 ) =>
        val nvisited1 = child1.size( visited )
        val nvisited2 = child2.size( nvisited1 )
        nvisited2 + ( ( this, nvisited2( child1 ) + nvisited2( child2 ) + 1 ) )
      case ETImp( child1, child2 ) =>
        val nvisited1 = child1.size( visited )
        val nvisited2 = child2.size( nvisited1 )
        nvisited2 + ( ( this, nvisited2( child1 ) + nvisited2( child2 ) + 1 ) )
      case ETMerge( child1, child2 ) =>
        val nvisited1 = child1.size( visited )
        val nvisited2 = child2.size( nvisited1 )
        nvisited2 + ( ( this, nvisited2( child1 ) + nvisited2( child2 ) + 1 ) )
      case ETWeakQuantifier( _, children ) =>
        val nvisited = children.foldLeft( visited )( ( vs, child ) => child._1.size( vs ) )
        val nsize = children.foldLeft( 1 )( ( s, child ) => s + nvisited( child._1 ) )
        nvisited + ( ( this, nsize ) )
      case ETStrongQuantifier( f, v, child ) =>
        val nvisited = child.size( visited )
        nvisited + ( ( this, nvisited( child ) + 1 ) )
      case ETSkolemQuantifier( f, v, child ) =>
        val nvisited = child.size( visited )
        nvisited + ( ( this, nvisited( child ) + 1 ) )
      case _ => throw new IllegalArgumentException( "Unhandled case in expansion tree size calculation: " + this )
    }
}

/**
 * Feigns being a subclass of ExpansionTreeWithMerges.
 * The apply methods in the pseudo case classes return ETs in case the arguments forming the children are ETs.
 * As the children are immutable, this ensures that the tree does not contain merges.
 * The classes also contain methods that have ETs as formal input and output parameters, which eliminates the need for
 * a lot of casting in client code.
 */
trait ExpansionTree extends ExpansionTreeWithMerges {
}

// generic equality for trees solely defined by node and children
trait NonTerminalNodeAWithEquality[+V, +E] extends NonTerminalNodeA[V, E] {
  override def equals( obj: scala.Any ): Boolean =
    ( this.getClass == obj.getClass ) &&
      ( this.node equals obj.asInstanceOf[NonTerminalNodeA[V, E]].node ) &&
      ( this.children equals obj.asInstanceOf[NonTerminalNodeA[V, E]].children )
}
trait TerminalNodeAWithEquality[+V, +E] extends TerminalNodeA[V, E] {
  override def equals( obj: scala.Any ): Boolean =
    ( this.getClass == obj.getClass ) &&
      ( this.node equals obj.asInstanceOf[TerminalNodeA[V, E]].node )
}

// with these, you can access the children of trees if you only know that they are binary and not their concrete type (which you sometimes know from proof construction)
trait BinaryExpansionTree extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula], Option[LambdaExpression]] {}
object BinaryExpansionTree {
  def unapply( et: ExpansionTree ) = et match {
    case bET: BinaryExpansionTree => Some( ( bET.children( 0 )._1.asInstanceOf[ExpansionTree], ( bET.children( 1 )._1.asInstanceOf[ExpansionTree] ) ) )
    case _                        => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case bET: BinaryExpansionTree => Some( ( bET.children( 0 )._1, bET.children( 1 )._1 ) )
    case _                        => None
  }
}
trait UnaryExpansionTree extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula], Option[LambdaExpression]] {}
object UnaryExpansionTree {
  def unapply( et: ExpansionTree ) = et match {
    case uET: UnaryExpansionTree => Some( ( uET.children( 0 )._1.asInstanceOf[ExpansionTree] ) )
    case _                       => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case uET: UnaryExpansionTree => Some( ( uET.children( 0 )._1 ) )
    case _                       => None
  }
}
/**
 * Represents Qx A +u1 E_1 ... +u_n E_n this way:
 * @param formula A
 * @param instances [ (E_1, u_1), ... , (E_n, u_1)
 */
class ETWeakQuantifier( val formula: HOLFormula, val instances: Seq[( ExpansionTreeWithMerges, LambdaExpression )] )
    extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula], Option[LambdaExpression]] {
  require( instances.map( _._2 ) == instances.map( _._2 ).distinct, "terms are not pairwise distinct" )

  lazy val node = Some( formula )
  lazy val children = instances.map( x => ( x._1, Some( x._2 ) ) )

}
object ETWeakQuantifier {
  // can't have another apply for ExpansionTree as type info gets lost with type erasure
  def apply( formula: HOLFormula, instances: Seq[( ExpansionTreeWithMerges, LambdaExpression )] ) =
    if ( instances.forall( { case ( et, _ ) => et.isInstanceOf[ExpansionTree] } ) ) new ETWeakQuantifier( formula, instances ) with ExpansionTree
    else new ETWeakQuantifier( formula, instances )

  def apply( formula: HOLFormula, instances: ( ExpansionTreeWithMerges, LambdaExpression )* )( implicit dummyImplicit: DummyImplicit ): ETWeakQuantifier = apply( formula, instances )
  // user of this functions must take care that no merges are passed here
  def applyWithoutMerge( formula: HOLFormula, instances: Seq[( ExpansionTree, LambdaExpression )] ) = new ETWeakQuantifier( formula, instances ) with ExpansionTree
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case weakQuantifier: ETWeakQuantifier => Some( ( weakQuantifier.formula, weakQuantifier.instances ) )
    case _                                => None
  }
  def unapply( et: ExpansionTree ): Option[( HOLFormula, Seq[( ExpansionTree, LambdaExpression )] )] = et match {
    case weakQuantifier: ETWeakQuantifier => Some( ( weakQuantifier.formula, weakQuantifier.instances.asInstanceOf[Seq[( ExpansionTree, LambdaExpression )]] ) )
    case _                                => None
  }
}

/**
 * Represents Qx A +u E:
 * @param formula A
 * @param variable u
 * @param selection E
 */
class ETStrongQuantifier( val formula: HOLFormula, val variable: Var, val selection: ExpansionTreeWithMerges )
    extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula], Option[LambdaExpression]] {
  lazy val node = Some( formula )
  lazy val children = List( Tuple2( selection, Some( variable ) ) )
}
object ETStrongQuantifier {
  def apply( formula: HOLFormula, variable: Var, selection: ExpansionTree ): ExpansionTree =
    // NOTE: this statement must not occur again in the other apply as it creates an own, distinct class, which scala treats as not equal even though it is exactly the same
    new ETStrongQuantifier( formula, variable, selection ) with ExpansionTree
  def apply( formula: HOLFormula, variable: Var, selection: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = selection match {
    case selectionET: ExpansionTree => ETStrongQuantifier( formula, variable, selectionET )
    case _                          => new ETStrongQuantifier( formula, variable, selection )
  }
  def unapply( et: ExpansionTree ) = et match {
    case strongQuantifier: ETStrongQuantifier => Some( ( strongQuantifier.formula, strongQuantifier.variable, strongQuantifier.selection.asInstanceOf[ExpansionTree] ) )
    case _                                    => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case strongQuantifier: ETStrongQuantifier => Some( ( strongQuantifier.formula, strongQuantifier.variable, strongQuantifier.selection ) )
    case _                                    => None
  }
}

/**
 * Represents Skolemized form of Qx A +u E:
 * @param formula A
 * @param skolem_constant u
 * @param selection E
 */
class ETSkolemQuantifier( val formula: HOLFormula, val skolem_constant: LambdaExpression, val selection: ExpansionTreeWithMerges )
    extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula], Option[LambdaExpression]] {
  lazy val node = Some( formula )
  lazy val children = List( Tuple2( selection, Some( skolem_constant ) ) )
}
object ETSkolemQuantifier {
  def apply( formula: HOLFormula, skolem_constant: LambdaExpression, selection: ExpansionTree ): ExpansionTree =
    // NOTE: this statement must not occur again in the other apply as it creates an own, distinct class, which scala treats as not equal even though it is exactly the same
    new ETSkolemQuantifier( formula, skolem_constant, selection ) with ExpansionTree
  def apply( formula: HOLFormula, skolem_constant: LambdaExpression, selection: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = selection match {
    case selectionET: ExpansionTree => ETSkolemQuantifier( formula, skolem_constant, selectionET )
    case _                          => new ETSkolemQuantifier( formula, skolem_constant, selection )
  }
  def unapply( et: ExpansionTree ) = et match {
    case sq: ETSkolemQuantifier => Some( ( sq.formula, sq.skolem_constant, sq.selection.asInstanceOf[ExpansionTree] ) )
    case _                      => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case sq: ETSkolemQuantifier => Some( ( sq.formula, sq.skolem_constant, sq.selection ) )
    case _                      => None
  }
}

case class ETMerge( left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges ) extends BinaryExpansionTree {
  val node = None
  lazy val children = List( Tuple2( left, None ), Tuple2( right, None ) )
}
object ETMerge {
  def apply( trees: Traversable[ExpansionTreeWithMerges] ): Option[ExpansionTreeWithMerges] =
    trees reduceOption { ETMerge( _, _ ) }
}

protected[expansionTrees] class ETAnd( val left: ExpansionTreeWithMerges, val right: ExpansionTreeWithMerges ) extends BinaryExpansionTree {
  val node = None
  lazy val children = List( Tuple2( left, None ), Tuple2( right, None ) )
}
object ETAnd {
  def apply( left: ExpansionTree, right: ExpansionTree ) = new ETAnd( left, right ) with ExpansionTree
  def apply( left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = ( left, right ) match {
    case ( leftET: ExpansionTree, rightET: ExpansionTree ) => ETAnd( leftET, rightET )
    case _ => new ETAnd( left, right )
  }
  def unapply( et: ExpansionTree ) = et match {
    case and: ETAnd => Some( ( and.left.asInstanceOf[ExpansionTree], and.right.asInstanceOf[ExpansionTree] ) )
    case _          => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case and: ETAnd => Some( ( and.left, and.right ) )
    case _          => None
  }
}

protected[expansionTrees] class ETOr( val left: ExpansionTreeWithMerges, val right: ExpansionTreeWithMerges ) extends BinaryExpansionTree {
  val node = None
  lazy val children = List( Tuple2( left, None ), Tuple2( right, None ) )
}
object ETOr {
  def apply( left: ExpansionTree, right: ExpansionTree ) = new ETOr( left, right ) with ExpansionTree
  def apply( left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = ( left, right ) match {
    case ( leftET: ExpansionTree, rightET: ExpansionTree ) => ETOr( leftET, rightET )
    case _ => new ETOr( left, right )
  }
  def unapply( et: ExpansionTree ) = et match {
    case or: ETOr => Some( ( or.left.asInstanceOf[ExpansionTree], or.right.asInstanceOf[ExpansionTree] ) )
    case _        => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case or: ETOr => Some( ( or.left, or.right ) )
    case _        => None
  }
}

protected[expansionTrees] class ETImp( val left: ExpansionTreeWithMerges, val right: ExpansionTreeWithMerges ) extends BinaryExpansionTree {
  val node = None
  lazy val children = List( Tuple2( left, None ), Tuple2( right, None ) )
}
object ETImp {
  def apply( left: ExpansionTree, right: ExpansionTree ) = new ETImp( left, right ) with ExpansionTree
  def apply( left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = ( left, right ) match {
    case ( leftET: ExpansionTree, rightET: ExpansionTree ) => ETImp( leftET, rightET )
    case _ => new ETImp( left, right )
  }
  def unapply( et: ExpansionTree ) = et match {
    case imp: ETImp => Some( ( imp.left.asInstanceOf[ExpansionTree], imp.right.asInstanceOf[ExpansionTree] ) )
    case _          => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case imp: ETImp => Some( ( imp.left, imp.right ) )
    case _          => None
  }
}

protected[expansionTrees] class ETNeg( val tree: ExpansionTreeWithMerges ) extends UnaryExpansionTree {
  val node = None
  lazy val children = List( Tuple2( tree, None ) )
}
object ETNeg {
  def apply( tree: ExpansionTree ) = new ETNeg( tree ) with ExpansionTree
  def apply( tree: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = tree match {
    case treeET: ExpansionTree => ETNeg( treeET )
    case _                     => new ETNeg( tree )
  }
  def unapply( et: ExpansionTree ) = et match {
    case neg: ETNeg => Some( ( neg.tree ).asInstanceOf[ExpansionTree] )
    case _          => None
  }
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case neg: ETNeg => Some( ( neg.tree ) )
    case _          => None
  }
}

case class ETAtom( atom: HOLAtom ) extends ExpansionTree with TerminalNodeAWithEquality[Option[HOLAtom], Option[LambdaExpression]] {
  lazy val node = Some( atom )
}

/**
 * Represents a weakening in an expansion tree, i.e. a subformula which is not
 * needed for making the deep formula a tautology.
 * @param formula the (weak) formula at this node
 */
case class ETWeakening( formula: HOLFormula ) extends ExpansionTree with TerminalNodeAWithEquality[Option[HOLFormula], Option[LambdaExpression]] {
  lazy val node = Some( formula )
}

case object ETTop extends ExpansionTree {
  lazy val node = Some( Top() )
}

case object ETBottom extends ExpansionTree {
  lazy val node = Some( Bottom() )
}

object ETInitialNode {
  def apply( f: HOLFormula ): ExpansionTree = f match {
    case Bottom()   => ETBottom
    case Top()      => ETTop
    case a: HOLAtom => ETAtom( a )
    case _          => throw new Exception( s"Cannot create initial node with formula $f." )
  }
}

/**
 * Returns number of quantifiers
 */
object quantRulesNumber {
  def apply( tree: ExpansionTreeWithMerges ): Int = tree match {
    case ETBottom         => 0
    case ETTop            => 0
    case ETAtom( f )      => 0
    case ETWeakening( f ) => 0
    case ETNeg( t1 )      => quantRulesNumber( t1 )
    case ETAnd( t1, t2 )  => quantRulesNumber( t1 ) + quantRulesNumber( t2 )
    case ETOr( t1, t2 )   => quantRulesNumber( t1 ) + quantRulesNumber( t2 )
    case ETImp( t1, t2 )  => quantRulesNumber( t1 ) + quantRulesNumber( t2 )
    case ETWeakQuantifier( _, children ) => children.foldRight( 0 ) {
      case ( ( et, _ ), sum ) => quantRulesNumber( et ) + 1 + sum
    }
    case ETStrongQuantifier( _, _, et ) => quantRulesNumber( et ) + 1
    case ETSkolemQuantifier( _, _, et ) => quantRulesNumber( et ) + 1
  }

  def apply( ep: ExpansionSequent ): Int = {
    val qAnt = ep.antecedent.foldLeft( 0 )( ( sum, et ) => quantRulesNumber( et ) + sum )
    val qSuc = ep.succedent.foldLeft( 0 )( ( sum, et ) => quantRulesNumber( et ) + sum )
    qAnt + qSuc
  }
}

object isQuantified {
  def apply( tree: ExpansionTreeWithMerges ): Boolean = tree match {
    case ETBottom                      => false
    case ETTop                         => false
    case ETAtom( _ )                   => false
    case ETWeakening( _ )              => false
    case ETNeg( t )                    => isQuantified( t )
    case ETAnd( t1, t2 )               => isQuantified( t1 ) || isQuantified( t2 )
    case ETOr( t1, t2 )                => isQuantified( t1 ) || isQuantified( t2 )
    case ETImp( t1, t2 )               => isQuantified( t1 ) || isQuantified( t2 )
    case ETWeakQuantifier( _, _ )      => true
    case ETStrongQuantifier( _, _, _ ) => true
    case ETSkolemQuantifier( _, _, _ ) => true
  }
}

object ExpansionSequent {
  def apply(): ExpansionSequent = Sequent()
  def apply( antecedent: Seq[ExpansionTree], succedent: Seq[ExpansionTree] ): ExpansionSequent =
    new ExpansionSequent( antecedent, succedent )
  def unapply( etSeq: ExpansionSequent ) = Some( etSeq.toTuple )
}

object toDeep {
  def apply( tree: ExpansionTreeWithMerges, pol: Int = 1 ): HOLFormula = tree match {
    case ETBottom         => Bottom()
    case ETTop            => Top()
    case ETAtom( f )      => f
    case ETWeakening( f ) => if ( pol > 0 ) Bottom() else Top()
    case ETNeg( t1 )      => Neg( toDeep( t1, -pol ) )
    case ETAnd( t1, t2 )  => And( toDeep( t1, pol ), toDeep( t2, pol ) )
    case ETOr( t1, t2 )   => Or( toDeep( t1, pol ), toDeep( t2, pol ) )
    case ETImp( t1, t2 )  => Imp( toDeep( t1, -pol ), toDeep( t2, pol ) )
    case ETWeakQuantifier( _, cs ) => {
      if ( pol > 0 )
        Or( cs.map( t => toDeep( t._1, pol ) ).toList )
      else
        And( cs.map( t => toDeep( t._1, pol ) ).toList )
    }
    case ETStrongQuantifier( _, _, t ) => toDeep( t, pol )
    case ETSkolemQuantifier( _, _, t ) => toDeep( t, pol ) //TODO: check if this is correct
  }

  def apply( expansionSequent: ExpansionSequent ): HOLSequent = {
    HOLSequent( expansionSequent.antecedent.map( toDeep.apply( _, -1 ) ), expansionSequent.succedent.map( toDeep.apply( _, 1 ) ) ) // compiler wants the applys here
  }
}

object toShallow {
  def apply( tree: ExpansionTreeWithMerges ): HOLFormula = tree match {
    case ETBottom                      => Bottom()
    case ETTop                         => Top()
    case ETAtom( f )                   => f
    case ETWeakening( f )              => f
    case ETNeg( t1 )                   => Neg( toShallow( t1 ) )
    case ETAnd( t1, t2 )               => And( toShallow( t1 ), toShallow( t2 ) )
    case ETOr( t1, t2 )                => Or( toShallow( t1 ), toShallow( t2 ) )
    case ETImp( t1, t2 )               => Imp( toShallow( t1 ), toShallow( t2 ) )
    case ETWeakQuantifier( f, _ )      => f
    case ETStrongQuantifier( f, _, _ ) => f
    case ETSkolemQuantifier( f, _, _ ) => f
    case ETMerge( t, _ )               => toShallow( t )
  }

  def apply( ep: ExpansionSequent ): HOLSequent = {
    val ant = ep.antecedent.map( et => toShallow( et ) )
    val succ = ep.succedent.map( et => toShallow( et ) )

    HOLSequent( ant, succ )
  }
}

object ExpansionProofToLK {
  /**
   * Translate an expansion proof to LK.
   * @param ep an expansion sequent whose deep sequent is a propositional tautology
   * @return an LKProof of the shallow sequent of ep
   */
  def apply( ep: ExpansionSequent ): at.logic.gapt.proofs.lk.LKProof = solve.expansionProofToLKProof( ep ).get
}

/**
 * Gets expansion tree of a formula from expansion sequent.
 */
object getETOfFormula {
  def apply( etSeq: ExpansionSequent, f: HOLFormula, isAntecedent: Boolean ): Option[ExpansionTree] = {
    getFromExpansionTreeList( if ( isAntecedent ) etSeq.antecedent else etSeq.succedent, f )
  }

  private def getFromExpansionTreeList( ets: Seq[ExpansionTree], f: HOLFormula ): Option[ExpansionTree] = ets match {
    case head +: tail =>
      if ( toShallow( head ) == f ) Some( head )
      else getFromExpansionTreeList( tail, f )
    case Seq() => None
  }
}

/**
 * Builds an expansion tree from a formula and a map from variables to terms.
 * The paremeter pos is true if  the formula is to be considered positive
 * (right side of the sequent).
 */
object formulaToExpansionTree {
  def apply( form: HOLFormula, pos: Boolean ): ExpansionTree = {
    assert( !containsQuantifier( form ) )
    apply( form, List(), pos )
  }

  def apply( form: HOLFormula, subs: List[_ <: Substitution], pos: Boolean ): ExpansionTree = {
    // form's quantified variables must be pairwise distinct
    assert( isInVNF( form ), "formulaToExpansionTree: bound variables are not pairwise distinct." )
    // substitutions should not have variable capture
    assert( subs.forall( s => s.domain.intersect( s.range ) == Nil ), "formulaToExpansionTree: substitutions have variable capture." )
    apply_( form, subs, pos )
  }

  private def apply_( form: HOLFormula, subs: List[_ <: Substitution], pos: Boolean ): ExpansionTree = form match {
    case a: HOLAtom    => ETAtom( a )
    case Neg( f )      => ETNeg( apply_( f, subs, !pos ) ).asInstanceOf[ExpansionTree]
    case And( f1, f2 ) => ETAnd( apply_( f1, subs, pos ), apply_( f2, subs, pos ) ).asInstanceOf[ExpansionTree]
    case Or( f1, f2 )  => ETOr( apply_( f1, subs, pos ), apply_( f2, subs, pos ) ).asInstanceOf[ExpansionTree]
    case Imp( f1, f2 ) => ETImp( apply_( f1, subs, !pos ), apply_( f2, subs, pos ) ).asInstanceOf[ExpansionTree]
    case All( v, f ) => pos match {
      case true => // Strong quantifier
        val valid_subs = subs.filter( s => s.domain.contains( v ) )
        assert( valid_subs.length == 1, ( "Found no substitutions for " + v + " in " + subs ) )
        val next_f = valid_subs.head( f )
        val ev = valid_subs.head( v ).asInstanceOf[Var]
        ETStrongQuantifier( form, ev, apply_( next_f, valid_subs, pos ) ).asInstanceOf[ExpansionTree]
      case false => // Weak quantifier
        ETWeakQuantifier( form, subs.filter( _.domain.contains( v ) ).groupBy( _( v ) ).toSeq map {
          case ( t, subsWithT ) =>
            val next_f = Substitution( v -> t )( f )
            ( apply_( next_f, subsWithT, pos ), t )
        } ).asInstanceOf[ExpansionTree]
    }
    case Ex( v, f ) => pos match {
      case true => // Weak quantifier
        ETWeakQuantifier( form, subs.filter( _.domain.contains( v ) ).groupBy( _( v ) ).toSeq map {
          case ( t, subsWithT ) =>
            val next_f = Substitution( v -> t )( f )
            ( apply_( next_f, subsWithT, pos ), t )
        } ).asInstanceOf[ExpansionTree]
      case false => // Strong quantifier
        val valid_subs = subs.filter( s => s.domain.contains( v ) )
        assert( valid_subs.length == 1 )
        val next_f = valid_subs.head( f )
        val ev = valid_subs.head( v ).asInstanceOf[Var]
        ETStrongQuantifier( form, ev, apply_( next_f, valid_subs, pos ) ).asInstanceOf[ExpansionTree]
    }
    case Top()    => ETTop
    case Bottom() => ETBottom
    case _        => throw new Exception( "Error transforming a formula into an expansion tree: " + form )
  }
}

/**
 * Returns the expansion sequent with certain expansions trees removed
 */
object removeFromExpansionSequent {
  /**
   * @param seq: specifies formulas to remove; formulas in the antecedent/consequent will remove expansion trees in the antecedent/consequent of the expansion tree
   *             expansion trees are removed if Sh(e) \in seq (using default equality, which is alpha equality)
   */
  def apply( etSeq: ExpansionSequent, seq: HOLSequent ): ExpansionSequent = {
    val ante = etSeq.antecedent.filterNot( et => seq.antecedent.contains( toShallow( et ) ) )
    val cons = etSeq.succedent.filterNot( et => seq.succedent.contains( toShallow( et ) ) )
    new ExpansionSequent( ante, cons )
  }
}

object substitute extends at.logic.gapt.utils.logging.Logger {
  /**
   * Perform substitution including propagation of merge nodes
   */
  def apply( s: Substitution, et: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = doApplySubstitution( s, et )

  def apply( s: Substitution, et: ExpansionTree ): ExpansionTree = doApplySubstitution( s, et ).asInstanceOf[ExpansionTree]

  def apply( s: Substitution, es: ExpansionSequent ): ExpansionSequent =
    ExpansionSequent( es.antecedent.map( apply( s, _ ) ), es.succedent.map( apply( s, _ ) ) )

  /**
   * Perform substitution _without_ propagation of merge nodes
   * Useful for tests, has to be extra method due to different return type
   */
  def applyNoMerge( s: Substitution, et: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = {
    doApplySubstitution( s, et )
  }

  private[expansionTrees] def doApplySubstitution( s: Substitution, et: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = et match {
    case ETBottom | ETTop => et
    case ETAtom( f )      => ETAtom( s( f ).asInstanceOf[HOLAtom] ) // FIXME: Is this even correct?
    case ETWeakening( f ) => ETWeakening( s( f ) )
    case ETNeg( t1 )      => ETNeg( doApplySubstitution( s, t1 ) )
    case ETAnd( t1, t2 )  => ETAnd( doApplySubstitution( s, t1 ), doApplySubstitution( s, t2 ) )
    case ETOr( t1, t2 )   => ETOr( doApplySubstitution( s, t1 ), doApplySubstitution( s, t2 ) )
    case ETImp( t1, t2 )  => ETImp( doApplySubstitution( s, t1 ), doApplySubstitution( s, t2 ) )
    case ETStrongQuantifier( f, v, selection ) =>
      ETStrongQuantifier( s( f ), s( v ).asInstanceOf[Var], doApplySubstitution( s, selection ) )
    case ETSkolemQuantifier( f, v, selection ) =>
      ETSkolemQuantifier( s( f ), s( v ), doApplySubstitution( s, selection ) )
    case ETWeakQuantifier( f, instances ) =>
      ETWeakQuantifier( s( f ), mergeWeakQuantifiers( Some( s ), instances ) )
    case ETMerge( t1, t2 ) => ETMerge( doApplySubstitution( s, t1 ), doApplySubstitution( s, t2 ) )
  }

  /**
   * If present, apply Substitution s to weak quantifier instances, then create merge nodes for duplicates
   */
  private[expansionTrees] def mergeWeakQuantifiers( s: Option[Substitution], instances: Seq[( ExpansionTreeWithMerges, LambdaExpression )] ): Seq[( ExpansionTreeWithMerges, LambdaExpression )] = {
    // through merging, some instances might disappear
    // keep map (substituted var -> [  ] ) to rebuild instances from it
    type InstList = ListBuffer[ExpansionTreeWithMerges]
    val newInstances = collection.mutable.LinkedHashMap[LambdaExpression, InstList]()
    s match {
      case Some( subst ) =>
        instances.foreach( { case ( et, expr ) => ( newInstances.getOrElseUpdate( subst.apply( expr ), new InstList ) += doApplySubstitution( subst, et ) ) } )
      case None =>
        instances.foreach( { case ( et, expr ) => ( newInstances.getOrElseUpdate( expr, new InstList ) += et ) } )
    }

    def createMergeNode( ets: Iterable[ExpansionTreeWithMerges] ): ExpansionTreeWithMerges = {
      ets.reduce( ( tree1, tree2 ) => ETMerge( tree1, tree2 ) )
    }

    newInstances.map( instance => ( createMergeNode( instance._2 ), instance._1 ) ).toList
  }
}

object merge extends at.logic.gapt.utils.logging.Logger {

  // Reduces all MergeNodes in the tree
  def apply( tree: ExpansionTreeWithMerges ): ExpansionTree = {
    main( tree, polarity = true )._1
  }

  def apply( expansionSequent: Sequent[ExpansionTreeWithMerges] ): ExpansionSequent =
    apply( expansionSequent.toTuple )

  // Reduces all MergeNodes in the sequent
  def apply( etSeq: ( Seq[ExpansionTreeWithMerges], Seq[ExpansionTreeWithMerges] ) ): ExpansionSequent = {
    val ( antecedent, succedent ) = etSeq
    val allTrees = antecedent ++ succedent
    val dnLine = sys.props( "line.separator" ) + sys.props( "line.separator" )

    trace( dnLine + "merge seq in: " + antecedent + " |- " + succedent )

    // apply main to all trees. if a substitution occurs, apply it to all trees and restart whole process as
    // substitutions can create merges (potentially everywhere).
    def applyRec( trees: Seq[ExpansionTreeWithMerges], index: Int ): Seq[ExpansionTreeWithMerges] = {
      if ( index == trees.length ) {
        trees
      } else {
        trace( dnLine + "merge on index: " + index + " tree: " + trees( index ) + " trees: " + trees )
        // define current tree and context, apply main and rebuild later
        val context = trees.take( index ) ++ trees.drop( index + 1 )
        val curTree = trees( index )

        trace( "old context:" + context )

        val isAntecedent = index < antecedent.length
        val polarity = if ( isAntecedent ) false else true

        val ( newTree, newContext, substitutionOccurred ) = main( curTree, polarity, context )

        trace( "new context:" + newContext )

        assert( newContext.length == context.length )

        applyRec(
          newContext.take( index ) ++ List( newTree ) ++ newContext.drop( index ),
          index = if ( substitutionOccurred ) { 0 } else { index + 1 }
        )
      }
    }

    val allNewTrees = applyRec( allTrees, 0 ).asInstanceOf[Seq[ExpansionTree]]

    trace( "merge seq out: " + allNewTrees )

    return new ExpansionSequent(
      allNewTrees.take( antecedent.length ),
      allNewTrees.drop( antecedent.length )
    )
  }

  /**
   * Outer merge loop. Call merge, handle substitution occurring during merge and repeat.
   * @param polarity: true for positive
   */
  private def main( tree: ExpansionTreeWithMerges, polarity: Boolean, context: Seq[ExpansionTreeWithMerges] = Nil, substitutionOccurred: Boolean = false ): ( ExpansionTree, Seq[ExpansionTreeWithMerges], Boolean ) = {
    trace( "merge in: " + tree )
    trace( "merge in context: " + context )

    val ( subst, et ) = detectAndMergeMergeNodes( tree, polarity )
    subst match {
      case Some( s ) => {
        trace( "substitution: " + s )
        main( substitute.applyNoMerge( s, et ), polarity, context.map( substitute.applyNoMerge( s, _ ) ), substitutionOccurred = true )
      }
      case None => {
        trace( "merge out: " + et )
        trace( "merge out context: " + context )
        ( et.asInstanceOf[ExpansionTree], context, substitutionOccurred )
      }

    }
  }

  /**
   * Called initially with root, search for merge nodes and calls doApplyMerge on the merge nodes
   * If a substitution is encountered, the current state of the ET is made explicit in the return value, consisting of the substitution and the current state
   * If no substitution is returned, the tree in the return value does not contain merge nodes
   * @param polarity: required for merging top and bottom.
   */
  private def detectAndMergeMergeNodes( tree: ExpansionTreeWithMerges, polarity: Boolean ): ( Option[Substitution], ExpansionTreeWithMerges ) = {

    // code which is required for all binary operators
    // @param leftPolarity: polarity of left child
    def start_op2( t1: ExpansionTreeWithMerges, t2: ExpansionTreeWithMerges,
                   OpFactory:    ( ExpansionTreeWithMerges, ExpansionTreeWithMerges ) => ExpansionTreeWithMerges,
                   leftPolarity: Boolean ): ( Option[Substitution], ExpansionTreeWithMerges ) = {
      val ( subst1, res1 ) = detectAndMergeMergeNodes( t1, leftPolarity )
      subst1 match {
        case Some( s: Substitution ) => // found substitution, need to return right here
          ( Some( s ), OpFactory( res1, t2 ) )
        case None => // no substitution, continue
          val ( subst2, res2 ) = detectAndMergeMergeNodes( t2, polarity )
          ( subst2, OpFactory( res1, res2 ) ) // might be Some(subst) or None
      }
    }

    tree match {
      case ETStrongQuantifier( f, v, sel ) =>
        val ( subst, res ) = detectAndMergeMergeNodes( sel, polarity )
        ( subst, ETStrongQuantifier( f, v, res ) )
      case ETSkolemQuantifier( f, sk, sel ) =>
        val ( subst, res ) = detectAndMergeMergeNodes( sel, polarity )
        ( subst, ETSkolemQuantifier( f, sk, res ) )
      case ETWeakQuantifier( f, instances ) => {
        var instancesPrime = new ListBuffer[( ExpansionTreeWithMerges, LambdaExpression )]
        // try to call merge on all instances
        // this is somewhat iterative in itself (stop on first substitution since we can't handle multiple substitutions at the same time)
        for ( instance <- instances ) {
          val ( et, expr ) = instance
          val ( subst, res ) = detectAndMergeMergeNodes( et, polarity )
          instancesPrime += Tuple2( res, expr )
          subst match {
            case Some( s: Substitution ) => {
              return ( Some( s ), ETWeakQuantifier( f, instancesPrime ++ instances.drop( instancesPrime.length ) ) )
            }
            case None =>
          }
        }
        // all instances done without substitution
        ( None, ETWeakQuantifier( f, instancesPrime.toList ) )
      }
      case ETAtom( f )      => ( None, ETAtom( f ) )
      case ETBottom | ETTop => ( None, tree )
      case ETWeakening( f ) => ( None, ETWeakening( f ) )
      case ETNeg( s1 ) => {
        val ( subst, res ) = detectAndMergeMergeNodes( s1, !polarity ) // changes polarity
        ( subst, ETNeg( res ) )
      }
      case ETAnd( t1, t2 )   => start_op2( t1, t2, ETAnd( _, _ ), leftPolarity = polarity )
      case ETOr( t1, t2 )    => start_op2( t1, t2, ETOr( _, _ ), leftPolarity = polarity )
      case ETImp( t1, t2 )   => start_op2( t1, t2, ETImp( _, _ ), leftPolarity = !polarity ) // changes polarity
      case ETMerge( t1, t2 ) => doApplyMerge( t1, t2, polarity )
    }
  } ensuring { res => toShallow( res._2 ) == toShallow( tree ) }

  /**
   * Returns either a substitution in case we have to do a substitution at the highest level or the merged tree
   * Call with children of merge node
   */
  private def doApplyMerge( tree1: ExpansionTreeWithMerges, tree2: ExpansionTreeWithMerges, polarity: Boolean ): ( Option[Substitution], ExpansionTreeWithMerges ) = {
    val nLine = sys.props( "line.separator" )
    trace( "apply merge called on: " + nLine + tree1 + nLine + tree2 )

    // similar as above, code which is required for all binary operators
    def start_op2( s1: ExpansionTreeWithMerges, t1: ExpansionTreeWithMerges,
                   s2: ExpansionTreeWithMerges, t2: ExpansionTreeWithMerges,
                   OpFactory:    ( ExpansionTreeWithMerges, ExpansionTreeWithMerges ) => ExpansionTreeWithMerges,
                   leftPolarity: Boolean ): ( Option[Substitution], ExpansionTreeWithMerges ) = {
      val ( subst1, res1 ) = doApplyMerge( s1, s2, leftPolarity )
      subst1 match {
        case Some( s: Substitution ) => ( Some( s ), OpFactory( res1, ETMerge( t1, t2 ) ) )
        case None =>
          val ( subst2, res2 ) = doApplyMerge( t1, t2, polarity )
          ( subst2, OpFactory( res1, res2 ) ) // might be Some(subst) or None
      }
    }

    ( tree1, tree2 ) match {
      case ( ETWeakening( _ ), _ )                          => detectAndMergeMergeNodes( tree2, polarity )
      case ( _, ETWeakening( _ ) )                          => detectAndMergeMergeNodes( tree1, polarity )

      //TODO: the f1 == f2 check is too strong if the proof contains contractions on paramodulated formulas. Find a better replacement.
      case ( ETAtom( f1 ), ETAtom( f2 ) ) /* if f1 == f2 */ => ( None, ETAtom( f1 ) )

      case ( ETTop, ETTop )                                 => ( None, ETTop )
      case ( ETBottom, ETBottom )                           => ( None, ETBottom )

      case ( ETStrongQuantifier( f1, v1, sel1 ), ETStrongQuantifier( f2, v2, sel2 ) ) if f1 == f2 =>
        trace( "encountered strong quantifier " + f1 + "; renaming " + v2 + " to " + v1 )
        return ( Some( Substitution( v2, v1 ) ), ETStrongQuantifier( f1, v1, ETMerge( sel1, sel2 ) ) )

      case ( ETSkolemQuantifier( f1, s1, sel1 ), ETSkolemQuantifier( f2, s2, sel2 ) ) if f1 == f2 =>
        // FIXME: this is (and was) completely broken in the case of s1 != s2, should perform global replacement of skolem symbols
        if ( s1 != s2 ) {
          // just do enough not to fail
          return doApplyMerge( replace( s2.asInstanceOf[Const], s1, tree1 ), replace( s2.asInstanceOf[Const], s1, tree2 ), polarity )
        }
        val ( subst, res ) = doApplyMerge( sel1, sel2, polarity )
        ( subst, ETSkolemQuantifier( f1, s1, res ) )

      case ( ETWeakQuantifier( f1, children1 ), ETWeakQuantifier( f2, children2 ) ) if f1 == f2 => {
        val newTree = ETWeakQuantifier( f1, substitute.mergeWeakQuantifiers( None, children1 ++ children2 ) )
        // merging might have caused merge-nodes and regular nodes, hence switch to detect-method
        detectAndMergeMergeNodes( newTree, polarity )
      }
      case ( ETNeg( s1 ), ETNeg( s2 ) ) => {
        val ( subst, res ) = doApplyMerge( s1, s2, !polarity ) // changes polarity
        ( subst, ETNeg( res ) )
      }
      case ( ETAnd( s1, t1 ), ETAnd( s2, t2 ) ) => start_op2( s1, t1, s2, t2, ETAnd( _, _ ), leftPolarity = polarity )
      case ( ETOr( s1, t1 ), ETOr( s2, t2 ) )   => start_op2( s1, t1, s2, t2, ETOr( _, _ ), leftPolarity = polarity )
      case ( ETImp( s1, t1 ), ETImp( s2, t2 ) ) => start_op2( s1, t1, s2, t2, ETImp( _, _ ), leftPolarity = !polarity ) //changes polarity
      case ( ETMerge( n1, n2 ), _ ) => { // we proceed top-bottom. Sometimes we need to propagate a merge below another merge, in which case the lower merge has to be resolved first
        val ( subst, res ) = doApplyMerge( n1, n2, polarity )
        subst match {
          case Some( s: Substitution ) => ( Some( s ), ETMerge( res, tree2 ) )
          case None                    => doApplyMerge( res, tree2, polarity )
        }
      }
      case ( _, ETMerge( n1, n2 ) ) => { // see above
        val ( subst, res ) = doApplyMerge( n1, n2, polarity )
        subst match {
          case Some( s: Substitution ) => ( Some( s ), ETMerge( res, tree2 ) )
          case None                    => doApplyMerge( tree1, res, polarity )
        }
      }
      case _ => throw new IllegalArgumentException( "Bug in merge in LKToExpansionProof. By Construction, the trees to be merge should have the same structure, which is violated for:" + nLine + tree1 + nLine + tree2 )
    }
  }
}

object replace {
  /**
   * Replaces all occurrences of the constants what by constants by in the expression where.
   * @param what what to replace
   * @param by what the insert instead
   * @param where in which expression
   * @return the resulting expression
   */
  def replaceAll( what: Const, by: LambdaExpression, where: HOLFormula ): HOLFormula = {
    replaceAll( what, by, where.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]
  }

  /**
   * Replaces all occurrences of the constants what by constants by in the expression where.
   * @param what what to replace
   * @param by what the insert instead
   * @param where in which expression
   * @return the resulting expression
   */
  def replaceAll( what: Const, by: LambdaExpression, where: LambdaExpression ): LambdaExpression = {
    if ( what != by ) //prevent cycles in replaceAllRec
      replaceAllRec( what, by, where )
    else
      where
  }
  @tailrec
  private def replaceAllRec( what: Const, by: LambdaExpression, where: LambdaExpression ): LambdaExpression = {
    HOLPosition.getPositions( where, _ == what ) match {
      case Nil => where
      case p :: _ =>
        replaceAllRec( what, by, HOLPosition.replace( where, p, by ) )
    }
  }

  /**
   * Duplicates the behaviour for Expansion Tress without merges
   * (the constructor is overloaded, so we need to make sure it is called with the correct type)
   * @param what constant name to replace
   * @param by constant to insert
   * @param where expansion tree where to replace
   * @return an et with all constants what replaced by constants by
   */
  def apply( what: Const, by: LambdaExpression, where: ExpansionTree ): ExpansionTree = where match {
    case ETTop | ETBottom => where
    case ETAtom( f )      => ETAtom( replaceAll( what, by, f ).asInstanceOf[HOLAtom] )
    case ETWeakening( f ) => ETWeakening( replaceAll( what, by, f ) )
    case ETNeg( l )       => ETNeg( apply( what, by, l ) )
    case ETAnd( l, r )    => ETAnd( apply( what, by, l ), apply( what, by, r ) )
    case ETOr( l, r )     => ETOr( apply( what, by, l ), apply( what, by, r ) )
    case ETImp( l, r )    => ETImp( apply( what, by, l ), apply( what, by, r ) )
    case ETWeakQuantifier( f, instances ) =>
      val children = instances.map( x =>
        ( apply( what, by, x._1 ), replaceAll( what, by, x._2 ) ) )
      ETWeakQuantifier.applyWithoutMerge( replaceAll( what, by, f ), children.asInstanceOf[Seq[( ExpansionTree, LambdaExpression )]] )
    case ETStrongQuantifier( f, v, tree ) =>
      ETStrongQuantifier( replaceAll( what, by, f ), v, apply( what, by, tree ) )
    case ETSkolemQuantifier( f, sk, tree ) =>
      ETSkolemQuantifier( replaceAll( what, by, f ), replaceAll( what, by, sk ), apply( what, by, tree ) )
  }

  /**
   * Replaces all occurrences of what by by in where.
   * @param what constant name to replace
   * @param by constant to insert
   * @param where expansion tree where to replace
   * @return an et with all constants what replaced by constants by
   */
  def apply( what: Const, by: LambdaExpression, where: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = where match {
    case ETTop | ETBottom => where
    case ETAtom( f )      => ETAtom( replaceAll( what, by, f ).asInstanceOf[HOLAtom] )
    case ETWeakening( f ) => ETWeakening( replaceAll( what, by, f ) )
    case ETNeg( l )       => ETNeg( apply( what, by, l ) )
    case ETAnd( l, r )    => ETAnd( apply( what, by, l ), apply( what, by, r ) )
    case ETOr( l, r )     => ETOr( apply( what, by, l ), apply( what, by, r ) )
    case ETImp( l, r )    => ETImp( apply( what, by, l ), apply( what, by, r ) )
    case ETWeakQuantifier( f, instances ) =>
      val children = instances.map( x =>
        ( apply( what, by, x._1 ), replaceAll( what, by, x._2 ) ) )
      ETWeakQuantifier( replaceAll( what, by, f ), children )
    case ETStrongQuantifier( f, v, tree ) =>
      ETStrongQuantifier( replaceAll( what, by, f ), v, apply( what, by, tree ) )
    case ETSkolemQuantifier( f, sk, tree ) =>
      ETSkolemQuantifier( replaceAll( what, by, f ), replaceAll( what, by, sk ), apply( what, by, tree ) )
    case ETMerge( l, r ) =>
      ETMerge( apply( what, by, l ), apply( what, by, r ) )
  }

}

object CleanStructure {
  /**
   * Shifts weakening nodes as far towards the root as possible.
   *
   * @param tree An ExpansionTree.
   * @return
   */
  def apply( tree: ExpansionTree ): ExpansionTree =
    tree match {
      case ETAtom( _ ) | ETWeakening( _ ) | ETTop | ETBottom => tree

      case ETNeg( sub ) =>
        val newSub = apply( sub )
        newSub match {
          case ETWeakening( _ ) => ETWeakening( toShallow( tree ) )
          case _                => ETNeg( newSub )
        }

      case ETAnd( left, right ) =>
        val newLeft = apply( left )
        val newRight = apply( right )

        ( newLeft, newRight ) match {
          case ( ETWeakening( _ ), ETWeakening( _ ) ) =>
            ETWeakening( toShallow( tree ) )
          case _ => ETAnd( newLeft, newRight )
        }

      case ETOr( left, right ) =>
        val newLeft = apply( left )
        val newRight = apply( right )

        ( newLeft, newRight ) match {
          case ( ETWeakening( _ ), ETWeakening( _ ) ) =>
            ETWeakening( toShallow( tree ) )
          case _ => ETOr( newLeft, newRight )
        }

      case ETImp( left, right ) =>
        val newLeft = apply( left )
        val newRight = apply( right )

        ( newLeft, newRight ) match {
          case ( ETWeakening( _ ), ETWeakening( _ ) ) =>
            ETWeakening( toShallow( tree ) )
          case _ => ETImp( newLeft, newRight )
        }

      case ETStrongQuantifier( f, v, sub ) =>
        val newSub = apply( sub )
        newSub match {
          case ETWeakening( _ ) => ETWeakening( f )
          case _                => ETStrongQuantifier( f, v, newSub )
        }

      case ETSkolemQuantifier( f, v, sub ) =>
        val newSub = apply( sub )
        newSub match {
          case ETWeakening( _ ) => ETWeakening( f )
          case _                => ETSkolemQuantifier( f, v, newSub )
        }

      case ETWeakQuantifier( f, instances ) =>
        val newInstances = instances map { p => ( apply( p._1 ), p._2 ) } filterNot { case ( ETWeakening( _ ), _ ) => true; case _ => false }

        newInstances match {
          case Seq() => ETWeakening( f )
          case _     => merge( ETWeakQuantifier( f, newInstances ) )
        }
    }
}

object replaceAtHOLPosition {
  def apply( et: ExpansionTreeWithMerges, pos: HOLPosition, exp: LambdaExpression ): ExpansionTreeWithMerges = {
    val rest = pos.tail
    ( et, pos.head ) match {
      case ( ETTop, _ ) | ( ETBottom, _ )               => et
      case ( ETAtom( formula ), _ )                     => ETAtom( formula.replace( pos, exp ).asInstanceOf[HOLAtom] )

      case ( ETWeakening( formula ), _ )                => ETWeakening( formula.replace( pos, exp ) )

      case ( ETNeg( sub ), 1 )                          => ETNeg( replaceAtHOLPosition( sub, rest, exp ) )

      case ( ETAnd( left, right ), 1 )                  => ETAnd( replaceAtHOLPosition( left, rest, exp ), right )
      case ( ETAnd( left, right ), 2 )                  => ETAnd( left, replaceAtHOLPosition( right, rest, exp ) )

      case ( ETOr( left, right ), 1 )                   => ETOr( replaceAtHOLPosition( left, rest, exp ), right )
      case ( ETOr( left, right ), 2 )                   => ETOr( left, replaceAtHOLPosition( right, rest, exp ) )

      case ( ETImp( left, right ), 1 )                  => ETImp( replaceAtHOLPosition( left, rest, exp ), right )
      case ( ETImp( left, right ), 2 )                  => ETImp( left, replaceAtHOLPosition( right, rest, exp ) )

      //FIXME: Quantifier cases are not entirely safe: What if the eigenvariable or the instances are replaced?
      case ( ETStrongQuantifier( formula, v, sub ), 1 ) => ETStrongQuantifier( formula.replace( pos, exp ), v, replaceAtHOLPosition( sub, rest, exp ) )
      case ( ETSkolemQuantifier( formula, v, sub ), 1 ) => ETSkolemQuantifier( formula.replace( pos, exp ), v, replaceAtHOLPosition( sub, rest, exp ) )

      case ( ETWeakQuantifier( formula, instances ), 1 ) =>
        val newInstances = instances map { p => ( replaceAtHOLPosition( p._1, rest, exp ), p._2 ) }
        ETWeakQuantifier( formula.replace( pos, exp ), newInstances )

      case ( ETMerge( left, right ), _ ) => ETMerge( replaceAtHOLPosition( left, pos, exp ), replaceAtHOLPosition( right, pos, exp ) )

      case _                             => throw new Exception( s"Can't perform replacement at position $pos in tree $et" )

    }
  }
}