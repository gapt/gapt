package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

/**
 * Formalisation of the tape-proof as described in C. Urban: Classical Logic
 * and Computation, PhD Thesis, Cambridge University, 2000.
 */
object tapeUrban {
  private val Seq( i, x, y, k, m, n, nprime ) = Seq( "i", "x", "y", "k", "m", "n", "n'" ) map {
    FOLVar( _ )
  }

  private val f = FOLFunctionConst( "f", 1 )
  private val leq = FOLAtomConst( "leq", 2 )
  private val lt = FOLAtomConst( "lt", 2 )
  private val max = FOLFunctionConst( "max", 2 )
  private val s = FOLFunctionConst( "s", 1 )
  private val zero = FOLConst( "0" )
  private val one = s( zero )

  private val A = All( x, Or( Eq( f( x ), zero ), Eq( f( x ), one ) ) )
  private val P = Ex( n, Ex( m, And( lt( n, m ), Eq( f( n ), f( m ) ) ) ) )
  private val T = All( i, All( x, All( y, Imp( And( Eq( f( y ), i ), Eq( f( x ), i ) ), Eq( f( x ), f( y ) ) ) ) ) )
  private val S = All( x, All( y, Imp( leq( s( x ), y ), lt( x, y ) ) ) )
  private val M1 = All( y, All( x, leq( x, max( x, y ) ) ) )
  private val M2 = All( y, All( x, leq( y, max( x, y ) ) ) )
  private val I0 = All( n, Ex( k, And( leq( n, k ), Eq( f( k ), zero ) ) ) )
  private val I1 = All( n, Ex( k, And( leq( n, k ), Eq( f( k ), one ) ) ) )
  private val Ii = All( n, Ex( k, And( leq( n, k ), Eq( f( k ), i ) ) ) )

  val tau = Lemma( Sequent(
    Seq( "M_1" -> FOLAtom( "M_1" ), "M_2" -> FOLAtom( "M_2" ), "A" -> FOLAtom( "A" ) ),
    Seq( "I0" -> FOLAtom( "I", Seq( zero ) ), "I1" -> FOLAtom( "I", Seq( one ) ) )
  ) ) {
    defR( "I1", I1 )
    allR( nprime, "I1" )
    defR( "I0", I0 )
    allR( n, "I0" )
    exR( max( n, nprime ), "I0" )
    exR( max( n, nprime ), "I1" )
    forget( "I0" ); forget( "I1" )
    andR( "I1_0" )
    forget( "A" ); forget( "M_1" ); forget( "I0_0" )
    defL( "M_2", M2 )
    chain( "M_2" )

    andR( "I0_0" )
    forget( "A" ); forget( "M_2" ); forget( "I1_0" )
    defL( "M_1", M1 )
    chain( "M_1" )

    forget( "M_1" ); forget( "M_2" )
    defL( "A", A )
    allL( max( n, nprime ), "A" )
    prop
  }

  val epsilon_i = Lemma( Sequent(
    Seq( "Ii" -> FOLAtom( "I", Seq( i ) ), "S" -> FOLAtom( "S" ), "T" -> FOLAtom( "T" ) ),
    Seq( "P" -> FOLAtom( "P" ) )
  ) ) {
    defL( "Ii", Ii )
    allL( zero, "Ii" )
    exL( n, "Ii_0" )
    allL( s( n ), "Ii" )
    exL( m, "Ii_1" )
    forget( "Ii" )
    defR( "P", P )
    exR( n, "P" )
    exR( m, "P_0" )
    forget( "P" ); forget( "P_0" )
    andL( "Ii_0" )
    andL( "Ii_1" )
    forget( "Ii_0_0" )
    andR( "P_0_0" )

    forget( "Ii_1_1" ); forget( "Ii_0_1" ); forget( "T" )
    defL( "S", S )
    chain( "S" )
    axiom

    forget( "Ii_1_0" ); forget( "S" )
    defL( "T", T )
    chain( "T" )
    axiom
    axiom
  }

  val sigma = Lemma( Sequent(
    Seq( "M_1" -> FOLAtom( "M_1" ), "M_2" -> FOLAtom( "M_2" ), "S" -> FOLAtom( "S" ), "T" -> FOLAtom( "T" ), "A" -> FOLAtom( "A" ) ),
    Seq( "P" -> FOLAtom( "P" ) )
  ) ) {
    cut( FOLAtom( "I", zero ), "I0" )
    cut( FOLAtom( "I", one ), "I1" )
    insert( tau )
    insert( epsilon_i )
    insert( epsilon_i )
  }
}

