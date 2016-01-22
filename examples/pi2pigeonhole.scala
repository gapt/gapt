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
      cut( All( x, Ex( y, lteq( x, y ) & ( f( y ) === zero ) ) ), "I0" )
      cut( All( x, Ex( y, lteq( x, y ) & ( f( y ) === one ) ) ), "I1" )

      forget( "t" ); decompose; escargot

      forget( "I0" )
      allL( zero, "I1" ); decompose
      allL( s( y ), "I1" ); decompose
      forget( "I1" ); escargot

      allL( zero, "I0" ); decompose
      allL( s( y ), "I0" ); decompose
      forget( "I0" ); escargot
    }
}
