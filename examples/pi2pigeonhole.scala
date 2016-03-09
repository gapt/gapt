package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.Sequent

object Pi2Pigeonhole {
  val zero = FOLConst( "0" )
  val s = FOLFunctionConst( "s", 1 )
  val one = s( zero )

  val M = FOLFunctionConst( "M", 2 )

  val f = FOLFunctionConst( "f", 1 )
  val lteq = FOLAtomConst( "<=", 2 )

  val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }

  val proof = Lemma(
    ( "maxlt" -> All( x, All( y, lteq( x, M( x, y ) ) & lteq( y, M( x, y ) ) ) ) ) +:
      ( "bound" -> All( x, Eq( f( x ), zero ) | Eq( f( x ), s( zero ) ) ) ) +:
      ( "ltsuc" -> All( x, All( y, lteq( s( x ), y ) --> lteq( x, y ) ) ) ) +:
      Sequent()
      :+ ( "t" -> Ex( x, Ex( y, lteq( s( x ), y ) & ( f( x ) === f( y ) ) ) ) )
  ) {
      cut( "I0", All( x, Ex( y, lteq( x, y ) & ( f( y ) === zero ) ) ) )
      cut( "I1", All( x, Ex( y, lteq( x, y ) & ( f( y ) === one ) ) ) )

      forget( "t" ); decompose; escargot

      forget( "I0" )
      allL( "I1", zero ); decompose
      allL( "I1", s( y ) ); decompose
      forget( "I1" ); escargot

      allL( "I0", zero ); decompose
      allL( "I0", s( y ) ); decompose
      forget( "I0" ); escargot
    }
}
