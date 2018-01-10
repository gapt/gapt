/*
 * Struct.scala
 *
 */

package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent

import scala.math.max

/**
 * The superclass for all struct elements: atom, negated atom, junction, times and the neutral elememts for the latter
 * two. For details refer to Bruno Woltzenlogel-Paleo's PhD Thesis.
 */
trait Struct {
  /**
   * Struct equality without taking the additional data into account.
   * @param that the struct to compare with
   * @return true if the structs are equal modulo data, false otherwise
   */
  def formula_equal( that: Struct ): Boolean

  /**
   * Calculates the size (number of nodes of the tree) of the struct.
   * @return the size of the struct
   */
  def size(): Int //total number of nodes

  /**
   * Calculates the maximum number of times-junction alternations of all paths from the root to one of the leaves.
   * The alternations are a measure for the complexity of the generated clause/sequent set.
   * @return the number of times-junction alternations
   */
  def alternations(): Int //number of alternations (includes duals)

  /**
   * Allows to access the calculus-specific data of the struct
   * @return the corresponding data element
   */

  def toFormula: Formula

  def label: Expr

  def children: Seq[Struct]
}

object Times {
  //create a series of of times applications and add the same data to each
  def apply( structs: Vector[Struct] ): Struct = structs match {
    case Vector()                  => EmptyTimesJunction()
    case EmptyTimesJunction() +: l => apply( l )
    case Vector( s1 )              => s1
    case s1 +: tail                => apply( s1, apply( tail ) )
  }
}

case class Times( left: Struct, right: Struct ) extends Struct {
  override def toString(): String = "(" + left + " ⊗ " + right + ")"
  override def formula_equal( s: Struct ) = s match {
    case Times( x, y ) => left.formula_equal( x ) && right.formula_equal( y )
    case _             => false
  }

  override def size() = 1 + left.size() + right.size()
  override def alternations() = {
    ( left, right ) match {
      case ( Times( _, _ ), Times( _, _ ) ) => max( left.alternations(), right.alternations() )
      case ( Times( _, _ ), _ )             => max( left.alternations(), 1 + right.alternations() )
      case ( _, Times( _, _ ) )             => max( 1 + left.alternations(), right.alternations() )
      case _                                => 1 + max( left.alternations(), right.alternations() )
    }
  }

  def toFormula = left.toFormula | right.toFormula

  def label = Const( "⊗", To ->: To ->: To )
  def children = Seq( left, right )

}

case class Plus( left: Struct, right: Struct ) extends Struct {
  override def toString(): String = "(" + left + " ⊕ " + right + ")"
  override def formula_equal( s: Struct ) = s match {
    case Plus( x, y ) => left.formula_equal( x ) && right.formula_equal( y )
    case _            => false
  }
  override def size() = 1 + left.size() + right.size()
  override def alternations() = {
    ( left, right ) match {
      case ( Plus( _, _ ), Plus( _, _ ) ) => max( left.alternations(), right.alternations() )
      case ( Plus( _, _ ), _ )            => max( left.alternations(), 1 + right.alternations() )
      case ( _, Plus( _, _ ) )            => max( 1 + left.alternations(), right.alternations() )
      case _                              => 1 + max( left.alternations(), right.alternations() )
    }
  }

  def toFormula = left.toFormula & right.toFormula

  def label = Const( "⊕", To ->: To ->: To )
  def children = Seq( left, right )
}
case class Dual( sub: Struct ) extends Struct {
  override def toString(): String = "~(" + sub + ")"
  override def formula_equal( s: Struct ) = s match {
    case Dual( x ) => sub.formula_equal( x )
    case _         => false
  }
  override def size() = 1 + sub.size()
  override def alternations() = {
    sub match {
      case Dual( _ ) => sub.alternations
      case _         => 1 + sub.size
    }
  }

  def toFormula = -sub.toFormula

  def label = Const( "~", To ->: To )
  def children = Seq( sub )
}
case class A( fo: Formula ) extends Struct { // Atomic Struct
  override def toString(): String = fo.toString
  override def formula_equal( s: Struct ) = s match {
    case A( x ) => fo syntaxEquals ( x )
    case _      => false
  }

  override def size() = 1
  override def alternations() = 0

  def toFormula = fo

  def label = fo
  def children = Seq()
}

case class CLS( proof: Expr, config: Sequent[Boolean] ) extends Struct { // Clause Set Symbol Struct
  override def toString(): String = {
    val Apps( Const( pn, _, _ ), vs ) = proof
    "CLS(" + pn + " , " + config.toString + " , " + vs.toString() + ")"
  }
  override def formula_equal( s: Struct ) = this == s
  override def size() = 1
  override def alternations() = 0

  def toFormula = {
    val Apps( Const( pn, _, _ ), vs ) = proof
    Atom( "CL" + "[" + pn + "," + config.toString + "]", vs )
  }
  def label = {
    val Apps( Const( pn, _, _ ), vs ) = proof
    Atom( "CL" + "[" + pn + "," + config.toString + "]", vs )
  }
  def children = Seq()
}

case class EmptyTimesJunction() extends Struct {
  override def toString(): String = "ε⊗"
  override def formula_equal( s: Struct ) = s match {
    case EmptyTimesJunction() => true
    case _                    => false
  }
  override def size() = 1
  override def alternations() = 0

  def toFormula = Bottom()

  def label = FOLAtom( "ε⊗" )
  def children = Seq()
}

case class EmptyPlusJunction() extends Struct {
  override def toString(): String = "ε⊕"
  override def formula_equal( s: Struct ) = s match {
    case EmptyPlusJunction() => true
    case _                   => false
  }
  override def size() = 1
  override def alternations() = 0

  def toFormula = Top()

  def label = FOLAtom( "ε⊕" )
  def children = Seq()
}

/* convenience object allowing to create and match a set of plus nodes */
object PlusN {
  def apply( l: List[Struct] ): Struct = l match {
    case Nil      => EmptyPlusJunction()
    case x :: Nil => x
    case x :: xs  => Plus( x, PlusN( xs ) )
  }

  def unapply( s: Struct ): Option[List[Struct]] = Some( unapply_( s ) )

  private def unapply_( s: Struct ): List[Struct] = s match {
    case Plus( l, r ) => unapply_( l ) ++ unapply_( r )
    case _            => s :: Nil
  }
}

//Returns all Schematic Leaves
object SchematicLeafs {
  def apply( l: Struct ): Set[Struct] = l match {
    case Times( le, r ) => SchematicLeafs( le ) ++ SchematicLeafs( r )
    case Plus( le, r )  => SchematicLeafs( le ) ++ SchematicLeafs( r )
    case CLS( x, y )    => Set[Struct]( l )
    case _              => Set[Struct]()

  }
}

