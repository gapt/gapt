package at.logic.gapt.examples.poset

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object proof {
  val f = FOLFunctionConst( "f", 2 )
  val Seq( u, v, w, x, y, z ) = Seq( "u", "v", "w", "x", "y", "z" ) map { FOLVar( _ ) }
  val Seq( a, b, c, d ) = Seq( "a", "b", "c", "d" ) map { FOLConst( _ ) }

  val trans = All( x, All( y, All( z, ( ( f( x, y ) === x ) & ( f( y, z ) === y ) ) --> ( f( x, z ) === x ) ) ) )
  val asymm = All( u, All( v, ( ( f( u, v ) === u ) & ( f( v, u ) === v ) ) --> ( u === v ) ) )

  val axioms =
    ( "eqrefl" -> All( x, x === x ) ) +:
      ( "eqsymm" -> All( x, All( y, ( x === y ) --> ( y === x ) ) ) ) +:
      ( "eqtrans" -> All( x, All( y, All( z, ( ( x === y ) & ( y === z ) ) --> ( x === z ) ) ) ) ) +:
      ( "eqfcongr" -> All( x, All( y, All( u, All( v, ( ( x === y ) & ( u === v ) ) --> ( f( x, u ) === f( y, v ) ) ) ) ) ) ) +:
      ( "fcomm" -> All( x, All( y, f( x, y ) === f( y, x ) ) ) ) +:
      ( "fassoc" -> All( x, All( y, All( z, f( f( x, y ), z ) === f( x, f( y, z ) ) ) ) ) ) +:
      Sequent()

  val transLemma = Lemma( axioms :+ ( "trans" -> trans ) ) {
    decompose
    chain( "eqtrans" ).subst( y -> f( f( x, y ), z ) )
    chain( "eqsymm" ); chain( "eqfcongr" ); prop; chain( "eqrefl" )
    chain( "eqtrans" ).subst( y -> f( x, f( y, z ) ) )
    chain( "fassoc" )
    chain( "eqtrans" ).subst( y -> f( x, y ) )
    chain( "eqfcongr" ); chain( "eqrefl" ); prop
    prop
  }

  val asymmLemma = Lemma( axioms :+ ( "asymm" -> asymm ) ) {
    decompose
    chain( "eqtrans" ).subst( y -> f( u, v ) )
    chain( "eqsymm" ); prop
    chain( "eqtrans" ).subst( y -> f( v, u ) )
    chain( "fcomm" )
    prop
  }

  val cycleImpliesEqual3 =
    Lemma( axioms :+ ( "goal" ->
      ( ( ( f( a, b ) === a ) & ( f( b, c ) === b ) & ( f( c, a ) === c ) ) --> ( ( a === b ) & ( b === c ) ) ) ) ) {
      cut( trans, "trans" )
      insert( transLemma )

      cut( asymm, "asymm" )
      insert( asymmLemma )

      // right side of the cut
      decompose; destruct( "goal_1" ) onAll ( chain( "asymm" ) andThen prop )

      // f(b,a)=b
      chain( "trans" ).subst( y -> c ); repeat( prop )

      // f(c,b)=c
      chain( "trans" ).subst( y -> a ); repeat( prop )
    }

  val cycleImpliesEqual4 =
    Lemma( axioms :+ ( "goal" ->
      ( ( ( f( a, b ) === a ) & ( f( b, c ) === b ) & ( f( c, d ) === c ) & ( f( d, a ) === d ) ) --> ( ( a === b ) & ( b === c ) & ( c === d ) ) ) ) ) {
      cut( trans, "trans" )
      insert( transLemma )

      cut( asymm, "asymm" )
      insert( asymmLemma )

      decompose

      // first show f(c,a)=c
      cut( f( c, a ) === c, "leq_c_a" ); forget( "goal_1" )
      chain( "trans" ).subst( y -> d ); prop; prop

      // and f(a,c)=a
      cut( f( a, c ) === a, "leq_a_c" ); forget( "goal_1" )
      chain( "trans" ).subst( y -> b ); prop; prop

      // now show the final goals
      repeat( destruct( "goal_1" ) )
      ( chain( "asymm" ) andThen prop ).onAllSubGoals

      // f(b,a)=b
      chain( "trans" ).subst( y -> c ); repeat( prop )

      // f(c,b)=c
      chain( "trans" ).subst( y -> a ); repeat( prop )

      // f(d,c)=c
      chain( "trans" ).subst( y -> a ); repeat( prop )
    }

}