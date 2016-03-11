package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object lattice {
  private val Seq( x, x_0, y, y_0, z, z_0 ) = Seq( "x", "x_0", "y", "y_0", "z", "z_0" ) map {
    FOLVar( _ )
  }

  private val cap = FOLFunctionConst( "cap", 2 )
  private val cup = FOLFunctionConst( "cup", 2 )
  private val leq = FOLAtomConst( "leq", 2 )

  private def r( x: HOLAtom, y: ( LambdaExpression, LambdaExpression )* ): HOLAtom =
    y.toList match {
      case ( y1, y2 ) :: ys => r( x.replace( x.find( y1 ), y2 ).asInstanceOf[HOLAtom], ys: _* )
      case Nil              => x
    }

  private val Seq( ax1, ax2, ax3, ax4, ax5, ax6 ) = Seq(
    Eq( cap( x, y ), cap( y, x ) ),
    Eq( cap( cap( x, y ), z ), cap( x, cap( y, z ) ) ),
    Eq( cap( x, x ), x ),
    Eq( cup( x, y ), cup( y, x ) ),
    Eq( cup( cup( x, y ), z ), cup( x, cup( y, z ) ) ),
    Eq( cup( x, x ), x )
  )

  private def leqUnfold( a: LambdaExpression, b: LambdaExpression ) = Eq( cap( a, b ), a )

  private val L1 = All( x, All( y, And(
    Imp( Eq( cap( x, y ), x ), Eq( cup( x, y ), y ) ),
    Imp( Eq( cup( x, y ), y ), Eq( cap( x, y ), x ) )
  ) ) )

  private val L2 = And(
    All( x, All( y, Eq( cup( cap( x, y ), x ), x ) ) ),
    All( x, All( y, Eq( cap( cup( x, y ), x ), x ) ) )
  )

  private val R = All( x, leq( x, x ) )
  private val AS = All( x, All( y, Imp( And( leq( x, y ), leq( y, x ) ), Eq( x, y ) ) ) )
  private val T = All( x, All( y, All( z, Imp( And( leq( x, y ), leq( y, z ) ), leq( x, z ) ) ) ) )
  private val POSET = And( FOLAtom( "R" ), And( FOLAtom( "AS" ), FOLAtom( "T" ) ) )
  private val GLB = All( x, All( y, And(
    And( leq( cap( x, y ), x ), leq( cap( x, y ), y ) ),
    All( z, Imp( And( leq( z, x ), leq( z, y ) ), leq( z, cap( x, y ) ) ) )
  ) ) )
  private val LUB = All( x, All( y, And(
    And( leq( x, cup( x, y ) ), leq( y, cup( x, y ) ) ),
    All( z, Imp( And( leq( x, z ), leq( y, z ) ), leq( cup( x, y ), z ) ) )
  ) ) )
  private val L3 = And( FOLAtom( "POSET" ), And( FOLAtom( "GLB" ), FOLAtom( "LUB" ) ) )

  val defs = Map(
    FOLAtom( "L1" ) -> L1,
    FOLAtom( "L2" ) -> L2,
    FOLAtom( "L3" ) -> L3,
    FOLAtom( "R" ) -> R,
    FOLAtom( "AS" ) -> AS,
    FOLAtom( "T" ) -> T,
    FOLAtom( "POSET" ) -> POSET,
    FOLAtom( "GLB" ) -> GLB,
    FOLAtom( "LUB" ) -> LUB,
    leq -> Abs( Seq( x, y ), leqUnfold( x, y ) )
  )

  //
  // In the equational background theory
  //

  def h1( s: LambdaExpression, t: LambdaExpression ) = {
    Lemma( Sequent( Nil, Seq( "a" -> Eq( cap( cap( s, t ), s ), cap( s, t ) ) ) ) ) {
      paramod( "a", r( ax1, ( x, cap( s, t ) ), ( y, s ) ), Eq( cap( s, cap( s, t ) ), cap( s, t ) ) )
      paramod( "a", r( ax2, ( x, s ), ( y, s ), ( z, t ) ), Eq( cap( cap( s, s ), t ), cap( s, t ) ) )
      paramod( "a", r( ax3, ( x, s ) ), Eq( cap( s, t ), cap( s, t ) ) )
      axiomRefl
    }
  }

  def h2( s: LambdaExpression, t: LambdaExpression ) = Lemma( Sequent( Nil, Seq( "a" -> Eq( cap( cap( s, t ), t ), cap( s, t ) ) ) ) ) {
    paramod( "a", r( ax2, ( x, s ), ( y, t ), ( z, t ) ), Eq( cap( s, cap( t, t ) ), cap( s, t ) ) )
    paramod( "a", r( ax3, ( x, t ) ), Eq( cap( s, t ), cap( s, t ) ) )
    axiomRefl
  }

  //
  // Left sub proof
  //

  // show that join is _least_ upper bound for \leq
  val p_6_a = All( z, Imp( And( leq( x_0, z ), leq( y_0, z ) ), leq( cup( x_0, y_0 ), z ) ) )
  val p_6_a_leq = All( z, Imp( And( leqUnfold( x_0, z ), leqUnfold( y_0, z ) ), leqUnfold( cup( x_0, y_0 ), z ) ) )

  val p_6 = Lemma( Sequent( Seq( "L1" -> FOLAtom( "L1" ) ), Seq( "a" -> p_6_a ) ) ) {
    defR( "a", p_6_a_leq )
    allR( z_0 )
    impR
    andL
    defL( "L1", L1 )
    allL( "L1", x_0, z_0 )
    andL( "L1_0" )
    impL( "L1_0_0" )
    prop
    allL( "L1", y_0, z_0 )
    andL( "L1_1" )
    impL( "L1_1_0" )
    prop
    allL( "L1", cup( x_0, y_0 ), z_0 )
    andL( "L1_2" )
    impL( "L1_2_1" )
    paramod( "L1_2_1", r( ax5, x -> x_0, y -> y_0, z -> z_0 ), Eq( cup( x_0, cup( y_0, z_0 ) ), z_0 ) )
    eqR( "L1_1_0", "L1_2_1" ).fromLeftToRight
    eqR( "L1_0_0", "L1_2_1" ).fromLeftToRight
    axiomRefl
    prop
  }

  // continues showing that join is upper bound for \leq
  def p_5_1( s: LambdaExpression, t: LambdaExpression ) = Lemma( Sequent( Seq( "L1" -> FOLAtom( "L1" ) ), Seq( "a" -> leq( s, cup( s, t ) ) ) ) ) {
    defR( "a", leqUnfold( s, cup( s, t ) ) )
    defL( "L1", L1 )
    allL( "L1", s, cup( s, t ) )
    andL
    impL( "L1_0_1" )
    paramod( "L1_0_1", r( ax5, x -> s, y -> s, z -> t ), Eq( cup( cup( s, s ), t ), cup( s, t ) ) )
    paramod( "L1_0_1", r( ax6, x -> s ), Eq( cup( s, t ), cup( s, t ) ) )
    axiomRefl
    prop
  }

  // show that join is upper bound for \leq
  val p_5 = Lemma( Sequent( Seq( "L1" -> FOLAtom( "L1" ) ), Seq( "LUB" -> FOLAtom( "LUB" ) ) ) ) {
    defR( "LUB", LUB )
    allR( "LUB", x_0 )
    allR( "LUB", y_0 )
    andR
    andR
    insert( p_5_1( x_0, y_0 ) )
    paramod( "LUB", r( ax4, x -> x_0, y -> y_0 ), leq( y_0, cup( y_0, x_0 ) ) )
    insert( p_5_1( y_0, x_0 ) )
    insert( p_6 )
  }

  //show that meet is _greatest_ lower bound for \leq
  val p_4_a = All( z, Imp( And( leq( z, x_0 ), leq( z, y_0 ) ), leq( z, cap( x_0, y_0 ) ) ) )
  val p_4_a_leq = All( z, Imp( And( leqUnfold( z, x_0 ), leqUnfold( z, y_0 ) ), leqUnfold( z, cap( x_0, y_0 ) ) ) )
  val p_4 = Lemma( Sequent( Nil, Seq( "a" -> p_4_a ) ) ) {
    defR( "a", p_4_a_leq )
    allR( z_0 )
    impR
    andL
    paramod( "a_1", r( ax2, x -> z_0, y -> x_0, z -> y_0 ), Eq( cap( cap( z_0, x_0 ), y_0 ), z_0 ) )
    eqR( "a_0_0", "a_1" ).fromLeftToRight
    eqR( "a_0_1", "a_1" ).fromLeftToRight
    axiomRefl
  }

  // finishes showing that meet is lower bound for \leq
  val p_3_1 = Lemma( Sequent( Nil, Seq( "a" -> leq( cap( x_0, y_0 ), y_0 ) ) ) ) {
    defR( "a", leqUnfold( cap( x_0, y_0 ), y_0 ) )
    insert( h2( x_0, y_0 ) )
  }

  // show that meet is lower bound for \leq
  val p_3 = Lemma( Sequent( Seq( "L1" -> FOLAtom( "L1" ) ), Seq( "a" -> And( FOLAtom( "GLB" ), FOLAtom( "LUB" ) ) ) ) ) {
    andR
    defR( "a", GLB )
    allR( "a", x_0 )
    allR( "a", y_0 )
    andR
    andR
    defR( "a", leqUnfold( cap( x_0, y_0 ), x_0 ) )
    insert( h1( x_0, y_0 ) )
    insert( p_3_1 )
    insert( p_4 )
    insert( p_5 )
  }

  // show transitivity
  val p_2 = Lemma( Sequent( Nil, Seq( "T" -> FOLAtom( "T" ) ) ) ) {
    defR( "T", T )
    allR( x_0 )
    allR( y_0 )
    allR( z_0 )
    impR
    andL
    defL( "T_0_0", leqUnfold( x_0, y_0 ) )
    defL( "T_0_1", leqUnfold( y_0, z_0 ) )
    defR( "T_1", leqUnfold( x_0, z_0 ) )
    eqR( "T_0_0", "T_1" ).fromRightToLeft
    eqR( "T_0_1", "T_1" ).to( Eq( cap( cap( x_0, y_0 ), z_0 ), cap( x_0, cap( y_0, z_0 ) ) ) )
    paramod( "T_1", r( ax2, x -> x_0, y -> y_0, z -> z_0 ), Eq( cap( cap( x_0, y_0 ), z_0 ), cap( cap( x_0, y_0 ), z_0 ) ) )
    axiomRefl
  }

  // show anti-symmetry
  val p_1 = Lemma( Sequent( Nil, Seq( "a" -> And( FOLAtom( "AS" ), FOLAtom( "T" ) ) ) ) ) {
    andR
    defR( "a", AS )
    allR( x_0 )
    allR( y_0 )
    impR
    andL
    defL( "a_0_0", leqUnfold( x_0, y_0 ) )
    defL( "a_0_1", leqUnfold( y_0, x_0 ) )
    paramod( "a_0_1", r( ax1, x -> x_0, y -> y_0 ), Eq( cap( x_0, y_0 ), y_0 ) )
    eqR( "a_0_0", "a_1" ).to( Eq( cap( x_0, y_0 ), y_0 ) )
    axiomLog
    insert( p_2 )
  }

  // split up POSET, show reflexivity
  val p1_3 = Lemma( Sequent( Seq( "L1" -> FOLAtom( "L1" ) ), Seq( "L3" -> FOLAtom( "L3" ) ) ) ) {
    defR( "L3", L3 )
    andR
    defR( "L3", POSET )
    andR
    defR( "L3", All( x, leqUnfold( x, x ) ) )
    allR( x_0 )
    paramod( "L3", r( ax3, x -> x_0 ), Eq( x_0, x_0 ) )
    axiomRefl
    insert( p_1 )
    insert( p_3 )
  }

  //
  // Right sub proof
  //

  // finishes r_2
  val r_2_1 = Lemma( Sequent( Seq( "LUB" -> FOLAtom( "LUB" ) ), Seq( "a" -> leq( x_0, cup( x_0, y_0 ) ) ) ) ) {
    defL( "LUB", LUB )
    allL( "LUB", x_0, y_0 )
    andL
    andL
    axiomLog
  }

  // absorption law 2 - difficult direction
  val r_2_a = All( z, Imp( And( leq( z, cup( x_0, y_0 ) ), leq( z, x_0 ) ), leq( z, cap( cup( x_0, y_0 ), x_0 ) ) ) )
  val r_2 = Lemma( Sequent( Seq( "LUB" -> FOLAtom( "LUB" ), "R" -> FOLAtom( "R" ), "a" -> r_2_a ), Seq( "b" -> leq( x_0, cap( cup( x_0, y_0 ), x_0 ) ) ) ) ) {
    allL( "a", x_0 )
    impL
    andR
    insert( r_2_1 )
    defL( "R", R )
    allL( "R", x_0 )
    axiomLog
    prop
  }

  // apply anti-symmetry to show absorption law 2 (+ easy direction)
  val q_2 = Lemma( Sequent( Seq( "GLB" -> FOLAtom( "GLB" ), "LUB" -> FOLAtom( "LUB" ), "R" -> FOLAtom( "R" ), "AS" -> FOLAtom( "AS" ) ), Seq( "a" -> All( x, All( y, Eq( cap( cup( x, y ), x ), x ) ) ) ) ) ) {
    allR( x_0 )
    allR( y_0 )
    defL( "AS", AS )
    allL( "AS", cap( cup( x_0, y_0 ), x_0 ), x_0 )
    forget( "AS" )
    impL( "AS_0" )
    defL( "GLB", GLB )
    allL( "GLB", cup( x_0, y_0 ), x_0 )
    forget( "GLB" )
    andL( "GLB_0" )
    andR
    destruct( "GLB_0_0" )
    axiomLog
    insert( r_2 )
    axiomLog
  }

  // finishes r_1
  val r_1_1 = Lemma( Sequent( Seq( "GLB" -> FOLAtom( "GLB" ) ), Seq( "a" -> leq( cap( x_0, y_0 ), x_0 ) ) ) ) {
    defL( "GLB", GLB )
    allL( "GLB", x_0, y_0 )
    forget( "GLB" )
    andL( "GLB_0" )
    andL( "GLB_0_0" )
    axiomLog
  }

  // absorption law 1 - difficult direction
  val r_1_a = All( z, Imp( And( leq( cap( x_0, y_0 ), z ), leq( x_0, z ) ), leq( cup( cap( x_0, y_0 ), x_0 ), z ) ) )
  val r_1 = Lemma( Sequent( Seq( "GLB" -> FOLAtom( "GLB" ), "R" -> FOLAtom( "R" ), "a" -> r_1_a ), Seq( "b" -> leq( cup( cap( x_0, y_0 ), x_0 ), x_0 ) ) ) ) {
    allL( "a", x_0 )
    impL
    andR
    insert( r_1_1 )
    defL( "R", R )
    allL( "R", x_0 )
    axiomLog
    prop
  }

  // apply anti-symmetry to show absorption law 1 (+ easy direction)
  val q_1 = Lemma( Sequent( Seq( "GLB" -> FOLAtom( "GLB" ), "LUB" -> FOLAtom( "LUB" ), "R" -> FOLAtom( "R" ), "AS" -> FOLAtom( "AS" ) ), Seq( "a" -> All( x, All( y, Eq( cup( cap( x, y ), x ), x ) ) ) ) ) ) {
    allR( x_0 )
    allR( y_0 )
    defL( "AS", AS )
    allL( "AS", cup( cap( x_0, y_0 ), x_0 ), x_0 )
    forget( "AS" )
    impL( "AS_0" )
    defL( "LUB", LUB )
    allL( "LUB", cap( x_0, y_0 ), x_0 )
    forget( "LUB" )
    andL( "LUB_0" )
    andL( "LUB_0_0" )
    andR
    insert( r_1 )
    axiomLog
    axiomLog
  }

  val p3_2 = Lemma( Sequent( Seq( "L3" -> FOLAtom( "L3" ) ), Seq( "L2" -> FOLAtom( "L2" ) ) ) ) {
    defL( "L3", L3 )
    decompose
    defL( "L3_0", POSET )
    decompose
    defR( "L2", L2 )
    andR
    insert( q_1 )
    insert( q_2 )
  }

  // Main proof
  val p = Lemma( Sequent( Seq( "L1" -> FOLAtom( "L1" ) ), Seq( "L2" -> FOLAtom( "L2" ) ) ) ) {
    cut( "L3", FOLAtom( "L3" ) )
    insert( p1_3 )
    insert( p3_2 )
  }
}
