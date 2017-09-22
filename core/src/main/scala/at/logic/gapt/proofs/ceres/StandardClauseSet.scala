/*
 * StandardClauseSet.scala
 *
 */

package at.logic.gapt.proofs.ceres

import at.logic.gapt.proofs.{ HOLClause, Sequent, SetSequent }
import at.logic.gapt.expr._

/**
 * Calculates the characteristic clause set
 */
class CharacteristicClauseSet[Data] {
  def apply( struct: Struct[Data] ): Set[SetSequent[Atom]] = struct match {
    case A( fo: Atom, _ ) => Set( SetSequent[Atom]( Sequent( Nil, List( fo ) ) ) )
    case A( Top(), _ )    => Set()
    case A( Bottom(), _ ) => Set( SetSequent[Atom]( Sequent( Nil, Nil ) ) )
    case A( f, _ ) =>
      throw new Exception( s"Encountered a formula $f as leaf in the struct. Can't convert it to a clause." )
    case Dual( A( fo: Atom, _ ) ) => Set( SetSequent[Atom]( Sequent( List( fo ), Nil ) ) )
    case Dual( A( Top(), _ ) )    => Set( SetSequent[Atom]( Sequent( Nil, Nil ) ) )
    case Dual( A( Bottom(), _ ) ) => Set()
    case Dual( A( f, _ ) ) =>
      throw new Exception( s"Encountered a formula $f as leaf in the struct. Can't convert it to a clause." )
    case EmptyPlusJunction()                 => Set()
    case EmptyTimesJunction()                => Set( SetSequent[Atom]( Sequent( Nil, Nil ) ) )
    case Plus( EmptyPlusJunction(), x )      => apply( x )
    case Plus( x, EmptyPlusJunction() )      => apply( x )
    case Plus( x, y )                        => apply( x ) ++ apply( y )
    case Times( EmptyTimesJunction(), x, _ ) => apply( x )
    case Times( x, EmptyTimesJunction(), _ ) => apply( x )
    case Times( A( f1, _ ), Dual( A( f2, _ ) ), _ ) if f1 == f2 => //would result in a tautology f :- f
      Set()
    case Times( Dual( A( f2, _ ) ), A( f1, _ ), _ ) if f1 == f2 => //would result in a tautology f :- f
      Set()
    case Times( x, y, _ ) =>
      val xs = apply( x )
      val ys = apply( y )
      xs.flatMap( ( x1: SetSequent[Atom] ) => ys.flatMap( ( y1: SetSequent[Atom] ) => {
        delta_compose( x1, y1 ) match {
          case Some( m ) => Set( m ).toTraversable
          case None      => Set().toTraversable
        }
      } ) )
    case CLS( proof, config, fv, _ ) =>
      val clauseSymbol: Atom = Atom( "CL", Seq( Const( proof, To ) ) ++ Seq( Const( "|", To ) ) ++ config.antecedent ++ Seq( Const( "⊢", To ) ) ++ config.succedent ++ Seq( Const( "|", To ) ) ++ fv )
      Set( SetSequent[Atom]( Sequent[Atom]( Nil, List( clauseSymbol ) ) ) )
    case _ => throw new Exception( "Unhandled case: " + struct )
  }

  private def compose[T]( fs1: Sequent[T], fs2: Sequent[T] ) = fs1 ++ fs2

  /* Like compose, but does not duplicate common terms */
  private def delta_compose[T]( fs1: SetSequent[T], fs2: SetSequent[T] ): Option[SetSequent[T]] = {
    val ante1 = fs1.sequent.antecedent.distinct.toSet ++ fs2.sequent.antecedent.distinct.toSet.diff( fs1.sequent.antecedent.distinct.toSet )
    val suc1 = fs1.sequent.succedent.distinct.toSet ++ fs2.sequent.succedent.distinct.toSet.diff( fs1.sequent.succedent.distinct.toSet )
    val anteSucInter = ante1 & suc1
    if ( anteSucInter.isEmpty ) Some( SetSequent[T]( Sequent[T]( ante1.toSeq, suc1.toSeq ) ) )
    else None

  }
}

object CharacteristicClauseSet {
  def apply[Data]( struct: Struct[Data] ): Set[HOLClause] = ( new CharacteristicClauseSet[Data] )( struct ).map( y => y.sequent )
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
    case Times( x, Dual( y ), aux ) if x.formula_equal( y ) =>
      //println("tautology deleted")
      EmptyPlusJunction()
    case Times( Dual( x ), y, aux ) if x.formula_equal( y ) =>
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

