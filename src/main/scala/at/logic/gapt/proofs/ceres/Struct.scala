/*
 * Struct.scala
 *
 */

package at.logic.gapt.proofs.ceres

import at.logic.gapt.proofs.occurrences.{ defaultFormulaOccurrenceFactory, FormulaOccurrence }
import at.logic.gapt.expr._
import at.logic.gapt.expr.SymbolA
import at.logic.gapt.utils.ds.trees.{ Tree, UnaryTree, BinaryTree, LeafTree }
import scala.math.max

/**
 * The superclass for all struct elements: atom, negated atom, junction, times and the neutral elememts for the latter
 * two. For details refer to Bruno Woltzenlogel-Oaleo's PhD Thesis.
 * @tparam Data the extraction algorithms for lksk and schema need to pass a list of additional data to the struct
 */
trait Struct[Data] {
  /**
   * Struct equality without taking the additional data into account.
   * @param that the struct to compare with
   * @return true if the structs are equal modulo data, false otherwise
   */
  def formula_equal( that: Struct[Data] ): Boolean

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
  def getData(): List[Data]
}

object Times {
  def apply[Data]( left: Struct[Data], right: Struct[Data], data: List[Data] ): Times[Data] =
    new Times( left, right, data )

  def apply[Data]( left: Struct[Data], right: Struct[Data] ): Times[Data] =
    new Times( left, right, Nil )

  //create a series of of times applications and add the same data to each
  def apply[Data]( structs: Seq[Struct[Data]], aux: List[Data] ): Struct[Data] = structs match {
    case Nil                       => EmptyTimesJunction()
    case EmptyTimesJunction() :: l => apply( l, aux )
    case s1 :: Nil                 => s1
    case s1 :: tail                => apply( s1, apply( tail, aux ), aux )
  }

  def unapply[Data]( t: Times[Data] ) = Some( ( t.left, t.right, t.data ) )
}

class Times[Data]( val left: Struct[Data], val right: Struct[Data], val data: List[Data] ) extends Struct[Data] {
  override def toString(): String = "(" + left + " ⊗ " + right + ")"
  override def formula_equal( s: Struct[Data] ) = s match {
    case Times( x, y, aux ) => left.formula_equal( x ) && right.formula_equal( y ) &&
      aux.diff( data ).isEmpty && data.diff( aux ).isEmpty
    case _ => false
  }

  override def size() = 1 + left.size() + right.size()
  override def alternations() = {
    ( left, right ) match {
      case ( Times( _, _, _ ), Times( _, _, _ ) ) => max( left.alternations(), right.alternations() )
      case ( Times( _, _, _ ), _ )                => max( left.alternations(), 1 + right.alternations() )
      case ( _, Times( _, _, _ ) )                => max( 1 + left.alternations(), right.alternations() )
      case _                                      => 1 + max( left.alternations(), right.alternations() )
    }
  }

  override def getData = data

}

case class Plus[Data]( left: Struct[Data], right: Struct[Data] ) extends Struct[Data] {
  override def toString(): String = "(" + left + " ⊕ " + right + ")"
  override def formula_equal( s: Struct[Data] ) = s match {
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
  override def getData = Nil
}
case class Dual[Data]( sub: Struct[Data] ) extends Struct[Data] {
  override def toString(): String = "~(" + sub + ")"
  override def formula_equal( s: Struct[Data] ) = s match {
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
  override def getData = Nil
}
case class A[Data]( fo: HOLFormula, data: List[Data] ) extends Struct[Data] { // Atomic Struct
  override def toString(): String = fo.toString
  override def formula_equal( s: Struct[Data] ) = s match {
    case A( x, _ ) => fo syntaxEquals ( x )
    case _         => false
  }

  override def size() = 1
  override def alternations() = 0
  override def getData = Nil
}

object A {
  def apply[Data]( fo: HOLFormula ): Struct[Data] = A[Data]( fo, Nil )
}

case class EmptyTimesJunction[Data]() extends Struct[Data] {
  override def toString(): String = "ε⊗"
  override def formula_equal( s: Struct[Data] ) = s match {
    case EmptyTimesJunction() => true
    case _                    => false
  }
  override def size() = 1
  override def alternations() = 0
  override def getData = Nil
}

case class EmptyPlusJunction[Data]() extends Struct[Data] {
  override def toString(): String = "ε⊕"
  override def formula_equal( s: Struct[Data] ) = s match {
    case EmptyPlusJunction() => true
    case _                   => false
  }
  override def size() = 1
  override def alternations() = 0
  override def getData = Nil
}

/* convenience object allowing to create and match a set of plus nodes */
object PlusN {
  def apply[Data]( l: List[Struct[Data]] ): Struct[Data] = l match {
    case Nil      => EmptyPlusJunction()
    case x :: Nil => x
    case x :: xs  => Plus( x, PlusN( xs ) )
  }

  def unapply[Data]( s: Struct[Data] ): Option[List[Struct[Data]]] = Some( unapply_( s ) )

  private def unapply_[Data]( s: Struct[Data] ): List[Struct[Data]] = s match {
    case Plus( l, r ) => unapply_( l ) ++ unapply_( r )
    case _            => s :: Nil
  }
}

