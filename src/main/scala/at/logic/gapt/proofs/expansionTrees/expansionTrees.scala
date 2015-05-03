package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.language.hol.algorithms.NaiveIncompleteMatchingAlgorithm
import at.logic.gapt.expr._
import at.logic.gapt.language.hol.{ HOLPosition, HOLSubstitution, getMatrix }
import at.logic.gapt.utils.ds.trees._
import at.logic.gapt.proofs.lk.base._
import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.collection.immutable.HashMap

/**
 * General class for expansion trees with pseudo case classes including for MergeNodes, which only occur during merging/substituting
 */
trait ExpansionTreeWithMerges extends TreeA[Option[Formula], Option[LambdaExpression]] {
  override def toString = this match {
    case ETAtom( f ) => "Atom(" + f.toString + ")"
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
      case ETAtom( v ) => visited + ( ( this, 1 ) )
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
trait BinaryExpansionTree extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[Formula], Option[LambdaExpression]] {}
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
trait UnaryExpansionTree extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[Formula], Option[LambdaExpression]] {}
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
class ETWeakQuantifier( val formula: Formula, val instances: Seq[( ExpansionTreeWithMerges, LambdaExpression )] )
    extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[Formula], Option[LambdaExpression]] {
  lazy val node = Some( formula )
  lazy val children = instances.map( x => ( x._1, Some( x._2 ) ) )

}
object ETWeakQuantifier {
  // can't have another apply for ExpansionTree as type info gets lost with type erasure
  def apply( formula: Formula, instances: Seq[( ExpansionTreeWithMerges, LambdaExpression )] ) =
    if ( instances.forall( { case ( et, _ ) => et.isInstanceOf[ExpansionTree] } ) ) new ETWeakQuantifier( formula, instances ) with ExpansionTree
    else new ETWeakQuantifier( formula, instances )
  // user of this functions must take care that no merges are passed here
  def applyWithoutMerge( formula: Formula, instances: Seq[( ExpansionTree, LambdaExpression )] ) = new ETWeakQuantifier( formula, instances ) with ExpansionTree
  def unapply( et: ExpansionTreeWithMerges ) = et match {
    case weakQuantifier: ETWeakQuantifier => Some( ( weakQuantifier.formula, weakQuantifier.instances ) )
    case _                                => None
  }
  def unapply( et: ExpansionTree ): Option[( Formula, Seq[( ExpansionTree, LambdaExpression )] )] = et match {
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
class ETStrongQuantifier( val formula: Formula, val variable: Var, val selection: ExpansionTreeWithMerges )
    extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[Formula], Option[LambdaExpression]] {
  lazy val node = Some( formula )
  lazy val children = List( Tuple2( selection, Some( variable ) ) )
}
object ETStrongQuantifier {
  def apply( formula: Formula, variable: Var, selection: ExpansionTree ): ExpansionTree =
    // NOTE: this statement must not occur again in the other apply as it creates an own, distinct class, which scala treats as not equal even though it is exactly the same
    new ETStrongQuantifier( formula, variable, selection ) with ExpansionTree
  def apply( formula: Formula, variable: Var, selection: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = selection match {
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
class ETSkolemQuantifier( val formula: Formula, val skolem_constant: LambdaExpression, val selection: ExpansionTreeWithMerges )
    extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[Formula], Option[LambdaExpression]] {
  lazy val node = Some( formula )
  lazy val children = List( Tuple2( selection, Some( skolem_constant ) ) )
}
object ETSkolemQuantifier {
  def apply( formula: Formula, skolem_constant: LambdaExpression, selection: ExpansionTree ): ExpansionTree =
    // NOTE: this statement must not occur again in the other apply as it creates an own, distinct class, which scala treats as not equal even though it is exactly the same
    new ETSkolemQuantifier( formula, skolem_constant, selection ) with ExpansionTree
  def apply( formula: Formula, skolem_constant: LambdaExpression, selection: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = selection match {
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

case class ETAtom( formula: Formula ) extends ExpansionTree with TerminalNodeAWithEquality[Option[Formula], Option[LambdaExpression]] {
  lazy val node = Some( formula )
}

/**
 * Returns number of quantifiers
 */
object quantRulesNumber {
  def apply( tree: ExpansionTreeWithMerges ): Int = tree match {
    case ETAtom( f )     => 0
    case ETNeg( t1 )     => quantRulesNumber( t1 )
    case ETAnd( t1, t2 ) => quantRulesNumber( t1 ) + quantRulesNumber( t2 )
    case ETOr( t1, t2 )  => quantRulesNumber( t1 ) + quantRulesNumber( t2 )
    case ETImp( t1, t2 ) => quantRulesNumber( t1 ) + quantRulesNumber( t2 )
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
    case ETAtom( _ )                   => false
    case ETNeg( t )                    => isQuantified( t )
    case ETAnd( t1, t2 )               => isQuantified( t1 ) || isQuantified( t2 )
    case ETOr( t1, t2 )                => isQuantified( t1 ) || isQuantified( t2 )
    case ETImp( t1, t2 )               => isQuantified( t1 ) || isQuantified( t2 )
    case ETWeakQuantifier( _, _ )      => true
    case ETStrongQuantifier( _, _, _ ) => true
    case ETSkolemQuantifier( _, _, _ ) => true
  }
}

class ExpansionSequent( val antecedent: Seq[ExpansionTree], val succedent: Seq[ExpansionTree] ) {
  def toTuple(): ( Seq[ExpansionTree], Seq[ExpansionTree] ) = {
    ( antecedent, succedent )
  }

  def map( f: ExpansionTree => ExpansionTree ): ExpansionSequent = {
    new ExpansionSequent( antecedent.map( f ), succedent.map( f ) )
  }

  def addToAntecedent( et: ExpansionTree ): ExpansionSequent = {
    new ExpansionSequent( et +: antecedent, succedent )
  }

  def addToSuccedent( et: ExpansionTree ): ExpansionSequent = {
    new ExpansionSequent( antecedent, et +: succedent )
  }

  def removeFromAntecedent( et: ExpansionTree ): ExpansionSequent = {
    require( antecedent.exists( _ eq et ) )
    new ExpansionSequent( antecedent.filterNot( _ eq et ), succedent )
  }

  def removeFromSuccedent( et: ExpansionTree ): ExpansionSequent = {
    require( succedent.exists( _ eq et ) )
    new ExpansionSequent( antecedent, succedent.filterNot( _ eq et ) )
  }

  def replaceInAntecedent( from: ExpansionTree, to: ExpansionTree ): ExpansionSequent = {
    require( antecedent.exists( _ eq from ) )
    new ExpansionSequent( antecedent.map( et => if ( et eq from ) to else et ), succedent )
  }

  def replaceInSuccedent( from: ExpansionTree, to: ExpansionTree ): ExpansionSequent = {
    require( succedent.exists( _ eq from ) )
    new ExpansionSequent( antecedent, succedent.map( et => if ( et eq from ) to else et ) )
  }

  override def toString: String = "ExpansionSequent(" + antecedent + ", " + succedent + ")"

  def canEqual( other: Any ): Boolean = other.isInstanceOf[ExpansionSequent]

  override def equals( other: Any ): Boolean = other match {
    case that: ExpansionSequent =>
      ( that canEqual this ) &&
        antecedent == that.antecedent &&
        succedent == that.succedent
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq( antecedent, succedent )
    state.map( _.hashCode() ).foldLeft( 0 )( ( a, b ) => 31 * a + b )
  }
}
object ExpansionSequent {
  def apply( antecedent: Seq[ExpansionTree], succedent: Seq[ExpansionTree] ) = new ExpansionSequent( antecedent, succedent )
  def unapply( etSeq: ExpansionSequent ) = Some( etSeq.toTuple() )
}

object toDeep {
  def apply( tree: ExpansionTreeWithMerges, pol: Int = 1 ): Formula = tree match {
    case ETAtom( f )     => f
    case ETNeg( t1 )     => Neg( toDeep( t1, -pol ) )
    case ETAnd( t1, t2 ) => And( toDeep( t1, pol ), toDeep( t2, pol ) )
    case ETOr( t1, t2 )  => Or( toDeep( t1, pol ), toDeep( t2, pol ) )
    case ETImp( t1, t2 ) => Imp( toDeep( t1, -pol ), toDeep( t2, pol ) )
    case ETWeakQuantifier( _, cs ) => {
      if ( pol > 0 )
        Or( cs.map( t => toDeep( t._1, pol ) ).toList )
      else
        And( cs.map( t => toDeep( t._1, pol ) ).toList )
    }
    case ETStrongQuantifier( _, _, t ) => toDeep( t, pol )
    case ETSkolemQuantifier( _, _, t ) => toDeep( t, pol ) //TODO: check if this is correct
  }

  def apply( expansionSequent: ExpansionSequent ): FSequent = {
    FSequent( expansionSequent.antecedent.map( toDeep.apply( _, -1 ) ), expansionSequent.succedent.map( toDeep.apply( _, 1 ) ) ) // compiler wants the applys here
  }
}

object toShallow {
  def apply( tree: ExpansionTreeWithMerges ): Formula = tree match {
    case ETAtom( f )                   => f
    case ETNeg( t1 )                   => Neg( toShallow( t1 ) )
    case ETAnd( t1, t2 )               => And( toShallow( t1 ), toShallow( t2 ) )
    case ETOr( t1, t2 )                => Or( toShallow( t1 ), toShallow( t2 ) )
    case ETImp( t1, t2 )               => Imp( toShallow( t1 ), toShallow( t2 ) )
    case ETWeakQuantifier( f, _ )      => f
    case ETStrongQuantifier( f, _, _ ) => f
  }

  def apply( ep: ExpansionSequent ): FSequent = {
    val ant = ep.antecedent.map( et => toShallow( et ) )
    val succ = ep.succedent.map( et => toShallow( et ) )

    FSequent( ant, succ )
  }
}

// Returns the end-sequent of the proof represented by this expansion tree
object toFSequent {
  def apply( ep: ExpansionSequent ): FSequent = {
    val ant = ep.antecedent.map( et => toShallow( et ) )
    val cons = ep.succedent.map( et => toShallow( et ) )

    FSequent( ant, cons )
  }
}

object getETOfFormula {
  def apply( etSeq: ExpansionSequent, f: Formula, isAntecedent: Boolean ): Option[ExpansionTree] = {
    getFromExpansionTreeList( if ( isAntecedent ) etSeq.antecedent else etSeq.succedent, f )
  }
  def getFromExpansionTreeList( ets: Seq[ExpansionTree], f: Formula ): Option[ExpansionTree] = ets match {
    case head :: tail =>
      if ( toShallow( head ) syntaxEquals f ) Some( head )
      else getFromExpansionTreeList( tail, f )
    case Nil => None
  }
}

/**
 * Builds an expansion tree from a quantifier free formula.
 */
object qFreeToExpansionTree {
  def apply( f: Formula ): ExpansionTree = f match {
    case HOLAtom( _, _ ) => ETAtom( f )
    case Neg( f )        => ETNeg( qFreeToExpansionTree( f ) ).asInstanceOf[ExpansionTree]
    case And( f1, f2 )   => ETAnd( qFreeToExpansionTree( f1 ), qFreeToExpansionTree( f2 ) ).asInstanceOf[ExpansionTree]
    case Or( f1, f2 )    => ETOr( qFreeToExpansionTree( f1 ), qFreeToExpansionTree( f2 ) ).asInstanceOf[ExpansionTree]
    case Imp( f1, f2 )   => ETImp( qFreeToExpansionTree( f1 ), qFreeToExpansionTree( f2 ) ).asInstanceOf[ExpansionTree]
    case _               => throw new Exception( "Error transforming a quantifier-free formula into an expansion tree: " + f )
  }
}

/**
 * Builds an expansion tree given a *prenex* formula and
 * its instances (or substitutions) using only weak quantifiers.
 *
 * NOTE: in principle, this could be implemented for non-prenex formulas.
 * What needs to be implemented is a method to remove the quantifiers of a
 * non-prenex formula (taking care about the renaming of variables).
 */
object prenexToExpansionTree {
  def apply( f: Formula, lst: List[Formula] ): ExpansionTree = {
    val fMatrix = getMatrix( f )

    // Each possible instance will generate an expansion tree, and they all 
    // have the same root.
    val children = lst.foldLeft( List[( ExpansionTreeWithMerges, LambdaExpression )]() ) {
      case ( acc, instance ) =>
        val subs = NaiveIncompleteMatchingAlgorithm.matchTerm( fMatrix, instance )
        val expTree = subs match {
          case Some( sub ) => apply_( f, sub )
          case None => throw new Exception( "ERROR: prenexToExpansionTree: No substitutions found for:\n" +
            "Matrix: " + fMatrix + "\nInstance: " + instance )
        }
        expTree match {
          case ETWeakQuantifier( _, lst ) => lst.toList ++ acc
          case _                          => throw new Exception( "ERROR: Quantifier-free formula?" )
        }
    }

    // TODO: merge edges with the same term.
    ETWeakQuantifier( f, children ).asInstanceOf[ExpansionTree] // can't contain merges currently, c.f. TODO above
  }

  def apply_( f: Formula, sub: HOLSubstitution ): ExpansionTreeWithMerges = f match {
    case All( v, form ) =>
      val t = sub( v )
      val one_sub = HOLSubstitution( v, t )
      val newf = one_sub( form )
      //val newf = f.instantiate(t.asInstanceOf[FOLTerm])
      ETWeakQuantifier( f, List( Tuple2( apply_( newf, sub ), t ) ) )
    case Ex( v, form ) =>
      val t = sub( v )
      val one_sub = HOLSubstitution( v, t )
      val newf = one_sub( form ).asInstanceOf[Formula]
      //val newf = f.instantiate(t.asInstanceOf[FOLTerm])
      ETWeakQuantifier( f, List( Tuple2( apply_( newf, sub ), t ) ) )
    case _ => qFreeToExpansionTree( f )
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
  def apply( etSeq: ExpansionSequent, seq: FSequent ): ExpansionSequent = {
    val ante = etSeq.antecedent.filter( et => !seq._1.contains( toShallow( et ) ) )
    val cons = etSeq.succedent.filter( et => !seq._2.contains( toShallow( et ) ) )
    new ExpansionSequent( ante, cons )
  }
}

object substitute extends at.logic.gapt.utils.logging.Logger {
  /**
   * Perform substitution including propagation of merge nodes
   */
  def apply( s: HOLSubstitution, et: ExpansionTreeWithMerges ): ExpansionTree = {
    val etSubstituted = doApplySubstitution( s, et )
    //merge(etSubstituted)
    etSubstituted.asInstanceOf[ExpansionTree]
  }

  /**
   * Perform substitution _without_ propagation of merge nodes
   * Useful for tests, has to be extra method due to different return type
   */
  def applyNoMerge( s: HOLSubstitution, et: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = {
    doApplySubstitution( s, et )
  }

  private[expansionTrees] def doApplySubstitution( s: HOLSubstitution, et: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = et match {
    case ETAtom( f )     => ETAtom( s.apply( f ) )
    case ETNeg( t1 )     => ETNeg( doApplySubstitution( s, t1 ) )
    case ETAnd( t1, t2 ) => ETAnd( doApplySubstitution( s, t1 ), doApplySubstitution( s, t2 ) )
    case ETOr( t1, t2 )  => ETOr( doApplySubstitution( s, t1 ), doApplySubstitution( s, t2 ) )
    case ETImp( t1, t2 ) => ETImp( doApplySubstitution( s, t1 ), doApplySubstitution( s, t2 ) )
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
  private[expansionTrees] def mergeWeakQuantifiers( s: Option[HOLSubstitution], instances: Seq[( ExpansionTreeWithMerges, LambdaExpression )] ): Seq[( ExpansionTreeWithMerges, LambdaExpression )] = {
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

  // Reduces all MergeNodes in the sequent
  def apply( etSeq: ( Seq[ExpansionTreeWithMerges], Seq[ExpansionTreeWithMerges] ) ): ExpansionSequent = {
    val ( antecedent, succedent ) = etSeq
    val allTrees = antecedent ++ succedent

    trace( "\n\nmerge seq in: " + antecedent + " |- " + succedent )

    // apply main to all trees. if a substitution occurs, apply it to all trees and restart whole process as
    // substitutions can create merges (potentially everywhere).
    def applyRec( trees: Seq[ExpansionTreeWithMerges], index: Int ): Seq[ExpansionTreeWithMerges] = {
      if ( index == trees.length ) {
        trees
      } else {
        trace( "\n\nmerge on index: " + index + " tree: " + trees( index ) + " trees: " + trees )
        // define current tree and context, apply main and rebuild later
        val context = trees.take( index ) ++ trees.drop( index + 1 )
        val curTree = trees( index )

        trace( "old context:" + context )

        val isAntecedent = index < antecedent.length
        val polarity = if ( isAntecedent ) false else true

        val ( newTree, newContext, substitutionOccurred ) = main( curTree, polarity, context )

        trace( "new context:" + newContext )

        assert( newContext.length == context.length )

        applyRec( newContext.take( index ) ++ List( newTree ) ++ newContext.drop( index ),
          index = if ( substitutionOccurred ) { 0 } else { index + 1 } )
      }
    }

    val allNewTrees = applyRec( allTrees, 0 ).asInstanceOf[Seq[ExpansionTree]]

    trace( "merge seq out: " + allNewTrees )

    return new ExpansionSequent(
      allNewTrees.take( antecedent.length ),
      allNewTrees.drop( antecedent.length ) )
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
  private def detectAndMergeMergeNodes( tree: ExpansionTreeWithMerges, polarity: Boolean ): ( Option[HOLSubstitution], ExpansionTreeWithMerges ) = {

    // code which is required for all binary operators
    // @param leftPolarity: polarity of left child
    def start_op2( t1: ExpansionTreeWithMerges, t2: ExpansionTreeWithMerges,
                   OpFactory: ( ExpansionTreeWithMerges, ExpansionTreeWithMerges ) => ExpansionTreeWithMerges,
                   leftPolarity: Boolean ): ( Option[HOLSubstitution], ExpansionTreeWithMerges ) = {
      val ( subst1, res1 ) = detectAndMergeMergeNodes( t1, leftPolarity )
      subst1 match {
        case Some( s: HOLSubstitution ) => // found substitution, need to return right here
          ( Some( s ), OpFactory( res1, t1 ) )
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
            case Some( s: HOLSubstitution ) => {
              return ( Some( s ), ETWeakQuantifier( f, instancesPrime ++ instances.drop( instancesPrime.length ) ) )
            }
            case None =>
          }
        }
        // all instances done without substitution
        ( None, ETWeakQuantifier( f, instancesPrime.toList ) )
      }
      case ETAtom( f ) => ( None, ETAtom( f ) )
      case ETNeg( s1 ) => {
        val ( subst, res ) = detectAndMergeMergeNodes( s1, !polarity ) // changes polarity
        ( subst, ETNeg( res ) )
      }
      case ETAnd( t1, t2 )   => start_op2( t1, t2, ETAnd( _, _ ), leftPolarity = polarity )
      case ETOr( t1, t2 )    => start_op2( t1, t2, ETOr( _, _ ), leftPolarity = polarity )
      case ETImp( t1, t2 )   => start_op2( t1, t2, ETImp( _, _ ), leftPolarity = !polarity ) // changes polarity
      case ETMerge( t1, t2 ) => doApplyMerge( t1, t2, polarity )
    }
  }

  /**
   * Returns either a substitution in case we have to do a substitution at the highest level or the merged tree
   * Call with children of merge node
   */
  private def doApplyMerge( tree1: ExpansionTreeWithMerges, tree2: ExpansionTreeWithMerges, polarity: Boolean ): ( Option[HOLSubstitution], ExpansionTreeWithMerges ) = {
    trace( "apply merge called on: \n" + tree1 + "\n" + tree2 )

    // similar as above, code which is required for all binary operators
    def start_op2( s1: ExpansionTreeWithMerges, t1: ExpansionTreeWithMerges,
                   s2: ExpansionTreeWithMerges, t2: ExpansionTreeWithMerges,
                   OpFactory: ( ExpansionTreeWithMerges, ExpansionTreeWithMerges ) => ExpansionTreeWithMerges,
                   leftPolarity: Boolean ): ( Option[HOLSubstitution], ExpansionTreeWithMerges ) = {
      val ( subst1, res1 ) = doApplyMerge( s1, s2, leftPolarity )
      subst1 match {
        case Some( s: HOLSubstitution ) => ( Some( s ), OpFactory( res1, ETMerge( t1, t2 ) ) )
        case None =>
          val ( subst2, res2 ) = doApplyMerge( t1, t2, polarity )
          ( subst2, OpFactory( res1, res2 ) ) // might be Some(subst) or None
      }
    }

    ( tree1, tree2 ) match {
      // top/bottom merging:
      // top [merge] A = A if !polarity
      // bottom [merge] A = A if polarity
      case ( ETAtom( Top() ), _ ) if !polarity              => detectAndMergeMergeNodes( tree2, polarity )
      case ( _, ETAtom( Top() ) ) if !polarity              => detectAndMergeMergeNodes( tree1, polarity )

      case ( ETAtom( Bottom() ), _ ) if polarity            => detectAndMergeMergeNodes( tree2, polarity )
      case ( _, ETAtom( Bottom() ) ) if polarity            => detectAndMergeMergeNodes( tree1, polarity )

      //TODO: the f1 == f2 check is too strong if the proof contains contractions on paramodulated formulas. Find a better replacement.
      case ( ETAtom( f1 ), ETAtom( f2 ) ) /* if f1 == f2 */ => ( None, ETAtom( f1 ) )

      case ( ETStrongQuantifier( f1, v1, sel1 ), ETStrongQuantifier( f2, v2, sel2 ) ) if f1 == f2 =>
        trace( "encountered strong quantifier " + f1 + "; renaming " + v2 + " to " + v1 )
        return ( Some( HOLSubstitution( v2, v1 ) ), ETStrongQuantifier( f1, v1, ETMerge( sel1, sel2 ) ) )

      case ( ETSkolemQuantifier( f1, s1, sel1 ), ETSkolemQuantifier( f2, s2, sel2 ) ) if f1 == f2 =>
        val sel2_ = if ( s1 != s2 ) {
          //TODO: we need to replace s2 by s1 in sel2, otherwise the merge operation fails
          //println(, "Can only merge Skolem Quantifier Nodes, if the skolem constants "+s1+" and "+s2+" are the same!")
          println( "Warning: merged skolem quantifiers are not equal - deep formula only valid modulo the equality " + s1 + " = " + s2 )
          ( s1, s2 ) match {
            case ( c: Const, d: Const ) =>
              replace( d, c, sel2 )
            case _ =>
              throw new Exception( "I have skolem terms " + s1 + " and " + s2 + " which are no consts and don't know what to do now." )
          }

        } else sel2
        //trace("encountered skolem quantifier "+f1+"; renaming "+v2+" to "+v1)
        return ( Some( HOLSubstitution() ), ETSkolemQuantifier( f1, s1, ETMerge( sel1, sel2_ ) ) )

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
          case Some( s: HOLSubstitution ) => ( Some( s ), ETMerge( res, tree2 ) )
          case None                       => doApplyMerge( res, tree2, polarity )
        }
      }
      case ( _, ETMerge( n1, n2 ) ) => { // see above
        val ( subst, res ) = doApplyMerge( n1, n2, polarity )
        subst match {
          case Some( s: HOLSubstitution ) => ( Some( s ), ETMerge( res, tree2 ) )
          case None                       => doApplyMerge( tree1, res, polarity )
        }
      }
      case _ => throw new IllegalArgumentException( "Bug in merge in extractExpansionSequent. By Construction, the trees to be merge should have the same structure, which is violated for:\n" + tree1 + "\n" + tree2 )
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
  def replaceAll( what: Const, by: Const, where: Formula ): Formula = {
    replaceAll( what, by, where.asInstanceOf[LambdaExpression] ).asInstanceOf[Formula]
  }

  /**
   * Replaces all occurrences of the constants what by constants by in the expression where.
   * @param what what to replace
   * @param by what the insert instead
   * @param where in which expression
   * @return the resulting expression
   */
  def replaceAll( what: Const, by: Const, where: LambdaExpression ): LambdaExpression = {
    if ( what != by ) //prevent cycles in replaceAllRec
      replaceAllRec( what, by, where )
    else
      where
  }
  @tailrec
  private def replaceAllRec( what: Const, by: Const, where: LambdaExpression ): LambdaExpression = {
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
  def apply( what: Const, by: Const, where: ExpansionTree ): ExpansionTree = where match {
    case ETAtom( f )   => ETAtom( replaceAll( what, by, f ) )
    case ETNeg( l )    => ETNeg( apply( what, by, l ) )
    case ETAnd( l, r ) => ETAnd( apply( what, by, l ), apply( what, by, r ) )
    case ETOr( l, r )  => ETOr( apply( what, by, l ), apply( what, by, r ) )
    case ETImp( l, r ) => ETImp( apply( what, by, l ), apply( what, by, r ) )
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
  def apply( what: Const, by: Const, where: ExpansionTreeWithMerges ): ExpansionTreeWithMerges = where match {
    case ETAtom( f )   => ETAtom( replaceAll( what, by, f ) )
    case ETNeg( l )    => ETNeg( apply( what, by, l ) )
    case ETAnd( l, r ) => ETAnd( apply( what, by, l ), apply( what, by, r ) )
    case ETOr( l, r )  => ETOr( apply( what, by, l ), apply( what, by, r ) )
    case ETImp( l, r ) => ETImp( apply( what, by, l ), apply( what, by, r ) )
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

/**
 * Create an expansion tree from a formula. Required for expansion tree extraction for weakenings.
 */
/*
object coerceFormulaToET {
  /**
   * @param f formula to coerce to ET
   * @param isAntecedent whether the formula appears in the antecedent or succedent. Relevant for quantifier instances.
   */
  def apply(f: Formula, isAntecedent: Boolean): ExpansionTree = {
    f match {
      case All(v, formula) =>
        if (isAntecedent) {
          StrongQuantifier(f, null, Atom(BottomC)) // TODO: better variable than null here?
        } else {
          WeakQuantifier(f, Nil).asInstanceOf[ExpansionTree] // contains no merges
        }
      case Ex(v, formula) =>
        if (isAntecedent) {
          WeakQuantifier(f, Nil).asInstanceOf[ExpansionTree] // contains no merges
        } else {
          StrongQuantifier(f, null, Atom(TopC))
        }
      case And(l, r) => And(coerceFormulaToET(l, isAntecedent), coerceFormulaToET(r, isAntecedent))
      case Or(l, r) => Or(coerceFormulaToET(l, isAntecedent), coerceFormulaToET(r, isAntecedent))
      case Imp(l, r) => Imp(coerceFormulaToET(l, isAntecedent), coerceFormulaToET(r, isAntecedent))
      case HOLAtom(_, _) => Atom(f)
    }
  }
}
*/

