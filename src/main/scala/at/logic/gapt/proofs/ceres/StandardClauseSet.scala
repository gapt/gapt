/*
 * StandardClauseSet.scala
 *
 */

package at.logic.gapt.proofs.ceres

import at.logic.gapt.proofs.{ HOLClause, HOLSequent }
import at.logic.gapt.expr._
import at.logic.gapt.utils.logging.Logger
import scala.annotation.tailrec
import scala.util.control.TailCalls._
import at.logic.gapt.proofs.ceres._

/**
 * Calculates the characteristic clause set
 */
class CharacteristicClauseSet[Data] {
  def apply( struct: Struct[Data] ): Set[HOLClause] = struct match {
    case A( fo, _ )                     => Set( HOLClause( Nil, List( fo ) ) )
    case Dual( A( fo, _ ) )             => Set( HOLClause( List( fo ), Nil ) )
    case EmptyPlusJunction()            => Set()
    case EmptyTimesJunction()           => Set( HOLClause( Nil, Nil ) )
    case Plus( EmptyPlusJunction(), x ) => apply( x )
    case Plus( x, EmptyPlusJunction() ) => apply( x )
    case Plus( A( f1, _ ), Dual( A( f2, _ ) ) ) if f1 == f2 =>
      Set()
    case Plus( Dual( A( f2, _ ) ), A( f1, _ ) ) if f1 == f2 =>
      Set()
    case Plus( x, y )                        => apply( x ) ++ apply( y )
    case Times( EmptyTimesJunction(), x, _ ) => apply( x )
    case Times( x, EmptyTimesJunction(), _ ) => apply( x )
    case Times( x, y, _ ) =>
      val xs = apply( x )
      val ys = apply( y )
      xs.flatMap( x1 => ys.flatMap( y1 => Set( delta_compose( x1, y1 ) ) ) )
    case _ => throw new Exception( "Unhandled case: " + struct )
  }

  private def compose( fs1: HOLClause, fs2: HOLClause ) = fs1 ++ fs2

  /* Like compose, but does not duplicate common terms */
  private def delta_compose( fs1: HOLClause, fs2: HOLClause ) = HOLClause(
    fs1.antecedent ++ fs2.antecedent.diff( fs1.antecedent ),
    fs1.succedent ++ fs2.succedent.diff( fs1.succedent )
  )
}

object CharacteristicClauseSet {
  def apply[Data]( struct: Struct[Data] ) = ( new CharacteristicClauseSet[Data] )( struct )
}

object SimplifyStruct {
  def apply[Data]( s: Struct[Data] ): Struct[Data] = s match {
    case EmptyPlusJunction()                 => s
    case EmptyTimesJunction()                => s
    case A( _, _ )                           => s
    case Dual( EmptyPlusJunction() )         => EmptyTimesJunction()
    case Dual( EmptyTimesJunction() )        => EmptyPlusJunction()
    case Dual( x )                           => Dual( SimplifyStruct( x ) )
    case Times( x, EmptyTimesJunction(), _ ) => SimplifyStruct( x )
    case Times( EmptyTimesJunction(), x, _ ) => SimplifyStruct( x )
    case Times( x, Dual( y: Struct[Data] ), aux ) if x.formula_equal( y ) =>
      //println("tautology deleted")
      EmptyPlusJunction()
    case Times( Dual( x: Struct[Data] ), y, aux ) if x.formula_equal( y ) =>
      //println("tautology deleted")
      EmptyPlusJunction()
    case Times( x, y, aux ) =>
      //TODO: adjust aux formulas, they are not needed for the css construction, so we can drop them,
      // but this method should be as general as possible
      Times( SimplifyStruct( x ), SimplifyStruct( y ), aux )
    case PlusN( terms ) =>
      //println("Checking pluses of "+terms)
      assert( terms.nonEmpty, "Implementation Error: PlusN always unapplies to at least one struct!" )
      val nonrendundant_terms = terms.foldLeft[List[Struct[Data]]]( Nil )( ( x, term ) => {
        val simple = SimplifyStruct( term )
        if ( x.filter( _.formula_equal( simple ) ).nonEmpty )
          x
        else
          simple :: x
      } )
      PlusN( nonrendundant_terms.reverse )

  }
}

