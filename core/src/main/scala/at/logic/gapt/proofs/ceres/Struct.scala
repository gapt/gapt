/*
 * Struct.scala
 *
 */

package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent

import scala.math.max

/**
 * The superclass for all struct elements: atom, negated atom, junction, times and the neutral elememts for the latter
 * two. For details refer to Bruno Woltzenlogel-Paleo's PhD Thesis.
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

  def toFormula: Formula

  def label: Expr

  def children: Seq[Struct[Data]]
}

object Times {
  //create a series of of times applications and add the same data to each
  def apply[Data]( structs: Vector[Struct[Data]], aux: List[Data] ): Struct[Data] = structs match {
    case Vector()                  => EmptyTimesJunction()
    case EmptyTimesJunction() +: l => apply( l, aux )
    case Vector( s1 )              => s1
    case s1 +: tail                => apply( s1, apply( tail, aux ), aux )
  }
}

case class Times[Data]( left: Struct[Data], right: Struct[Data], data: List[Data] = Nil ) extends Struct[Data] {
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

  def toFormula = left.toFormula | right.toFormula

  def label = Const( "⊗", To -> ( To -> To ) )
  def children = Seq( left, right )

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

  def toFormula = left.toFormula & right.toFormula

  def label = Const( "⊕", To -> ( To -> To ) )
  def children = Seq( left, right )
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

  def toFormula = -sub.toFormula

  def label = Const( "~", To -> To )
  def children = Seq( sub )
}
case class A[Data]( fo: Formula, data: List[Data] ) extends Struct[Data] { // Atomic Struct
  override def toString(): String = fo.toString
  override def formula_equal( s: Struct[Data] ) = s match {
    case A( x, _ ) => fo syntaxEquals ( x )
    case _         => false
  }

  override def size() = 1
  override def alternations() = 0
  override def getData = Nil

  def toFormula = fo

  def label = fo
  def children = Seq()
}

object A {
  def apply[Data]( fo: Formula ): Struct[Data] = A[Data]( fo, Nil )
}

case class CLS[Data]( proof: String, config: HOLSequent, fv: Seq[FOLTerm], data: List[Data] ) extends Struct[Data] { // Clause Set Symbol Struct
  override def toString(): String = "CLS(" + proof + " , " + config.toString + " , " + fv.toString() + ")"
  override def formula_equal( s: Struct[Data] ) = s match {
    case CLS( n, c, f, w ) => n.matches( proof ) && c.equals( config ) && f.equals( fv ) && w.equals( data )
    case _                 => false
  }
  override def size() = 1
  override def alternations() = 0
  override def getData = Nil

  def toFormula = FOLAtom( "CL" + "[" + proof + "," + config.toString + "]", fv )

  def label = FOLAtom( "CL" + "[" + proof + "," + config.toString + "]", fv )
  def children = Seq()
}
object CLS {
  def apply[Data]( Proof: String, config: HOLSequent, fv: Seq[FOLTerm] ): Struct[Data] = CLS[Data]( Proof, config, fv )
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

  def toFormula = Bottom()

  def label = FOLAtom( "ε⊗" )
  def children = Seq()
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

  def toFormula = Top()

  def label = FOLAtom( "ε⊕" )
  def children = Seq()
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

//Returns all Schematic Leaves
object SchematicLeafs {
  def apply( l: Struct[Nothing] ): Set[Struct[Nothing]] = l match {
    case Times( le, r, _ ) => SchematicLeafs( le ) ++ SchematicLeafs( r )
    case Plus( le, r )     => SchematicLeafs( le ) ++ SchematicLeafs( r )
    case CLS( x, y, z, w ) => Set[Struct[Nothing]]( l )
    case _                 => Set[Struct[Nothing]]()

  }
}

