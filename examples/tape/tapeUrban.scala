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
    exR( "I0", max( n, nprime ) )
    exR( "I1", max( n, nprime ) )
    forget( "I0", "I1" )
    andR( "I1_0" )
    forget( "A", "M_1", "I0_0" )
    defL( "M_2", M2 )
    chain( "M_2" )

    andR( "I0_0" )
    forget( "A", "M_2", "I1_0" )
    defL( "M_1", M1 )
    chain( "M_1" )

    forget( "M_1", "M_2" )
    defL( "A", A )
    allL( "A", max( n, nprime ) )
    prop
  }

  val epsilon_i = Lemma( Sequent(
    Seq( "Ii" -> FOLAtom( "I", Seq( i ) ), "S" -> FOLAtom( "S" ), "T" -> FOLAtom( "T" ) ),
    Seq( "P" -> FOLAtom( "P" ) )
  ) ) {
    defL( "Ii", Ii )
    allL( "Ii", zero )
    exL( n, "Ii_0" )
    allL( "Ii", s( n ) )
    exL( m, "Ii_1" )
    forget( "Ii" )
    defR( "P", P )
    exR( "P", n, m )
    forget( "P" )
    andL( "Ii_0" )
    andL( "Ii_1" )
    forget( "Ii_0_0" )
    andR( "P_0" )

    forget( "Ii_1_1", "Ii_0_1", "T" )
    defL( "S", S )
    chain( "S" )
    axiom

    forget( "Ii_1_0", "S" )
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

  val defs = Map(
    FOLAtomConst( "I", 1 ) -> Abs( i, Ii ),
    FOLAtom( "A" ) -> A,
    FOLAtom( "M_1" ) -> M1,
    FOLAtom( "M_2" ) -> M2,
    FOLAtom( "S" ) -> S,
    FOLAtom( "T" ) -> T,
    FOLAtom( "P" ) -> P
  )
}

