package at.logic.gapt.examples.poset

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object proof {
  private val f = FOLFunctionConst( "f", 2 )
  private val Seq( u, v, w, x, y, z ) = Seq( "u", "v", "w", "x", "y", "z" ) map { FOLVar( _ ) }
  private val Seq( a, b, c ) = Seq( "a", "b", "c" ) map { FOLConst( _ ) }

  val cycleImpliesEqual =
    Lemma(
      ( "eqrefl" -> All( x, x === x ) ) +:
        ( "eqsymm" -> All( x, All( y, ( x === y ) --> ( y === x ) ) ) ) +:
        ( "eqtrans" -> All( x, All( y, All( z, ( ( x === y ) & ( y === z ) ) --> ( x === z ) ) ) ) ) +:
        ( "eqfcongr" -> All( x, All( y, All( u, All( v, ( ( x === y ) & ( u === v ) ) --> ( f( x, u ) === f( y, v ) ) ) ) ) ) ) +:
        ( "fcomm" -> All( x, All( y, f( x, y ) === f( y, x ) ) ) ) +:
        ( "fassoc" -> All( x, All( y, All( z, f( f( x, y ), z ) === f( x, f( y, z ) ) ) ) ) ) +:
        Sequent()
        :+ ( "goal" -> ( ( ( f( a, b ) === a ) & ( f( b, c ) === b ) & ( f( c, a ) === c ) ) --> ( ( a === b ) & ( b === c ) ) ) )
    ) {
        cut(
          All( x, All( y, All( z, ( ( f( x, y ) === x ) & ( f( y, z ) === y ) ) --> ( f( x, z ) === x ) ) ) )
            & All( u, All( v, ( ( f( u, v ) === u ) & ( f( v, u ) === v ) ) --> ( u === v ) ) ),
          "cf"
        )

        forget( "goal" )
        destruct( "cf" ) onAll decompose

        // transitivity
        chain( "eqtrans" ).subst( y -> f( f( x, y ), z ) )
        chain( "eqsymm" ); chain( "eqfcongr" ); prop; chain( "eqrefl" )
        chain( "eqtrans" ).subst( y -> f( x, f( y, z ) ) )
        chain( "fassoc" )
        chain( "eqtrans" ).subst( y -> f( x, y ) )
        chain( "eqfcongr" ); chain( "eqrefl" ); prop
        prop

        // anti-symmetry
        chain( "eqtrans" ).subst( y -> f( u, v ) )
        chain( "eqsymm" ); prop
        chain( "eqtrans" ).subst( y -> f( v, u ) )
        chain( "fcomm" )
        prop

        // right side of the cut
        decompose; destruct( "goal_1" ) onAll ( chain( "cf_1" ) andThen prop )

        // f(b,a)=b
        chain( "cf_0" ).subst( y -> c ); repeat( prop )

        // f(c,b)=c
        chain( "cf_0" ).subst( y -> a ); repeat( prop )

      }

}