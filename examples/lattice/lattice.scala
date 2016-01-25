package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }

object lattice {
  private val Seq( x, x_0, y, y_0, z, z_0 ) = Seq( "x", "x_0", "y", "y_0", "z", "z_0" ) map {
    FOLVar( _ )
  }

  private val cap = FOLFunctionConst( "cap", 2 )
  private val cup = FOLFunctionConst( "cup", 2 )

  private val Seq( ax1, ax2, ax3, ax4, ax5, ax6 ) = Seq(
    All( x, All( y, Eq( cap( x, y ), cap( y, x ) ) ) ),
    All( x, All( y, All( z, Eq( cap( cap( x, y ), z ), cap( x, cap( y, z ) ) ) ) ) ),
    All( x, Eq( cap( x, x ), x ) ),
    All( x, All( y, Eq( cup( x, y ), cup( y, x ) ) ) ),
    All( x, All( y, All( z, Eq( cup( cup( x, y ), z ), cup( x, cup( y, z ) ) ) ) ) ),
    All( x, Eq( cup( x, x ), x ) )
  )

  private def leq( x: LambdaExpression, y: LambdaExpression ) = Eq( cap( x, y ), x )

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
  private val POSET = And( R, And( AS, T ) )
  private val GLB = All( x, All( y, And(
    And( leq( cap( x, y ), x ), leq( cap( x, y ), y ) ),
    All( z, Imp( And( leq( z, x ), leq( z, y ) ), leq( z, cap( x, y ) ) ) )
  ) ) )
  private val LUB = All( x, All( y, And(
    And( leq( x, cup( x, y ) ), leq( y, cup( x, y ) ) ),
    All( z, Imp( And( leq( x, z ), leq( y, z ) ), leq( cup( x, y ), z ) ) )
  ) ) )
  private val L3 = And( POSET, And( GLB, LUB ) )

  //
  // In the equational background theory
  //

  def h1( s: LambdaExpression, t: LambdaExpression ) = Lemma( Sequent( Seq( "ax1" -> ax1, "ax2" -> ax2, "ax3" -> ax3 ), Seq( "a" -> Eq( cap( cap( s, t ), s ), cap( s, t ) ) ) ) ) {
    allL( cap( s, t ), "ax1" )
    allL( s, "ax1_0" )
    eqR( "ax1_0_0", "a" ).fromLeftToRight
    allL( s, "ax2" )
    allL( s, "ax2_0" )
    allL( t, "ax2_0_0" )
    eqR( "ax2_0_0_0", "a" ).fromRightToLeft
    allL( s, "ax3" )
    eqR( "ax3_0", "a" ).fromLeftToRight
    axiomRefl
  }

  def h2( s: LambdaExpression, t: LambdaExpression ) = Lemma( Sequent( Seq( "ax2" -> ax2, "ax3" -> ax3 ), Seq( "a" -> Eq( cap( cap( s, t ), t ), cap( s, t ) ) ) ) ) {
    allL( s, "ax2" )
    allL( t, "ax2_0" )
    allL( t, "ax2_0_0" )
    eqR( "ax2_0_0_0", "a" ).fromLeftToRight
    allL( t, "ax3" )
    eqR( "ax3_0", "a" ).fromLeftToRight
    axiomRefl
  }

  //
  // Left sub proof
  //

  // show that join is _least_ upper bound for \leq
  val p_6 = Lemma( Sequent( Seq( "ax5" -> ax5, "L1" -> L1 ), Seq( "a" -> All( z, Imp( And( leq( x_0, z ), leq( y_0, z ) ), leq( cup( x_0, y_0 ), z ) ) ) ) ) ) {
    allR( z_0 )
    impR
    andL
    allL( x_0, "L1" )
    allL( z_0, "L1_0" )
    andL( "L1_0_0" )
    impL( "L1_0_0_0" )
    prop
    allL( y_0, "L1" )
    allL( z_0, "L1_1" )
    andL( "L1_1_0" )
    impL( "L1_1_0_0" )
    prop
    allL( cup( x_0, y_0 ), "L1" )
    allL( z_0, "L1_2" )
    andL( "L1_2_0" )
    impL( "L1_2_0_1" )
    allL( x_0, "ax5" )
    allL( y_0, "ax5_0" )
    allL( z_0, "ax5_0_0" )
    eqR( "ax5_0_0_0", "L1_2_0_1" ).fromLeftToRight
    eqR( "L1_1_0_0", "L1_2_0_1" ).fromLeftToRight
    eqR( "L1_0_0_0", "L1_2_0_1" ).fromLeftToRight
    axiomRefl
    prop
  }

  // continues showing that join is upper bound for \leq
  def p_5_1( s: LambdaExpression, t: LambdaExpression ) = Lemma( Sequent( Seq( "ax5" -> ax5, "ax6" -> ax6, "L1" -> L1 ), Seq( "a" -> leq( s, cup( s, t ) ) ) ) ) {
    allL( s, "L1" )
    allL( cup( s, t ), "L1_0" )
    andL
    impL( "L1_0_0_1" )
    allL( s, "ax5" )
    allL( s, "ax5_0" )
    allL( t, "ax5_0_0" )
    allL( s, "ax6" )
    eqR( "ax5_0_0_0", "L1_0_0_1" ).fromRightToLeft
    eqR( "ax6_0", "L1_0_0_1" ).fromLeftToRight
    axiomRefl
    prop
  }

  // show that join is upper bound for \leq
  val p_5 = Lemma( Sequent( Seq( "ax4" -> ax4, "ax5" -> ax5, "ax6" -> ax6, "L1" -> L1 ), Seq( "LUB" -> LUB ) ) ) {
    allR( x_0, "LUB" )
    allR( y_0, "LUB" )
    andR
    andR
    insert( p_5_1( x_0, y_0 ) )
    allL( x_0, "ax4" )
    allL( y_0, "ax4_0" )
    eqR( "ax4_0_0", "LUB" ).fromLeftToRight
    insert( p_5_1( y_0, x_0 ) )
    insert( p_6 )
  }

  //show that meet is _greatest_ lower bound for \leq
  val p_4 = Lemma( Sequent( Seq( "ax2" -> ax2 ), Seq( "a" -> All( z, Imp( And( leq( z, x_0 ), leq( z, y_0 ) ), leq( z, cap( x_0, y_0 ) ) ) ) ) ) ) {
    allR( z_0 )
    impR
    andL
    allL( z_0, "ax2" )
    allL( x_0, "ax2_0" )
    allL( y_0, "ax2_0_0" )
    eqR( "ax2_0_0_0", "a_1" ).fromRightToLeft
    eqR( "a_0_0", "a_1" ).fromLeftToRight
    eqR( "a_0_1", "a_1" ).fromLeftToRight
    axiomRefl
  }

  // finishes showing that meet is lower bound for \leq
  val p_3_1 = Lemma( Sequent( Seq( "ax2" -> ax2, "ax3" -> ax3 ), Seq( "a" -> leq( cap( x_0, y_0 ), y_0 ) ) ) ) {
    insert( h2( x_0, y_0 ) )
  }

  // show that meet is lower bound for \leq
  val p_3 = Lemma( Sequent( Seq( "ax1" -> ax1, "ax2" -> ax2, "ax3" -> ax3, "ax4" -> ax4, "ax5" -> ax5, "ax6" -> ax6, "L1" -> L1 ), Seq( "a" -> And( GLB, LUB ) ) ) ) {
    andR
    allR( x_0, "a" )
    allR( y_0, "a" )
    andR
    andR
    insert( h1( x_0, y_0 ) )
    insert( p_3_1 )
    insert( p_4 )
    insert( p_5 )
  }

  // show transitivity
  val p_2 = Lemma( Sequent( Seq( "ax2" -> ax2 ), Seq( "T" -> T ) ) ) {
    allR( x_0 )
    allR( y_0 )
    allR( z_0 )
    impR
    andL
    eqR( "T_0_0", "T_1" ).fromRightToLeft
    eqR( "T_0_1", "T_1" ).to( Eq( cap( cap( x_0, y_0 ), z_0 ), cap( x_0, cap( y_0, z_0 ) ) ) )
    allL( x_0, "ax2" )
    allL( y_0, "ax2_0" )
    allL( z_0, "ax2_0_0" )
    eqR( "ax2_0_0_0", "T_1" ).to( Eq( cap( cap( x_0, y_0 ), z_0 ), cap( cap( x_0, y_0 ), z_0 ) ) )
    axiomRefl
  }

  // show anti-symmetry
  val p_1 = Lemma( Sequent( Seq( "ax1" -> ax1, "ax2" -> ax2 ), Seq( "a" -> And( AS, T ) ) ) ) {
    andR
    allR( x_0 )
    allR( y_0 )
    impR
    andL
    allL( x_0, "ax1" )
    allL( y_0, "ax1_0" )
    eqR( "a_0_0", "a_1" ).to( Eq( cap( x_0, y_0 ), y_0 ) )
    eqR( "a_0_1", "a_1" ).to( Eq( cap( x_0, y_0 ), cap( y_0, x_0 ) ) )
    eqR( "ax1_0_0", "a_1" ).to( Eq( cap( x_0, y_0 ), cap( x_0, y_0 ) ) )
    axiomRefl
    insert( p_2 )
  }

  // split up POSET, show reflexivity
  val p1_3 = Lemma( Sequent( Seq( "ax1" -> ax1, "ax2" -> ax2, "ax3" -> ax3, "ax4" -> ax4, "ax5" -> ax5, "ax6" -> ax6, "L1" -> L1 ), Seq( "L3" -> L3 ) ) ) {
    andR
    andR
    allR( x_0 )
    allL( x_0, "ax3" )
    eqR( "ax3_0", "L3" ).fromLeftToRight
    axiomRefl
    insert( p_1 )
    insert( p_3 )
  }

  //
  // Right sub proof
  //

  // finishes r_2
  val r_2_1 = Lemma( Sequent( Seq( "LUB" -> LUB ), Seq( "a" -> leq( x_0, cup( x_0, y_0 ) ) ) ) ) {
    allL( x_0, "LUB" )
    allL( y_0, "LUB_0" )
    andL
    andL
    axiomLog
  }

  // absorption law 2 - difficult direction
  val r_2_a = All( z, Imp( And( leq( z, cup( x_0, y_0 ) ), leq( z, x_0 ) ), leq( z, cap( cup( x_0, y_0 ), x_0 ) ) ) )
  val r_2 = Lemma( Sequent( Seq( "a" -> r_2_a, "LUB" -> LUB, "R" -> R ), Seq( "b" -> leq( x_0, cap( cup( x_0, y_0 ), x_0 ) ) ) ) ) {
    allL( x_0, "a" )
    impL
    andR
    insert( r_2_1 )
    allL( x_0, "R" )
    axiomLog
    prop
  }

  // apply anti-symmetry to show absorption law 2 (+ easy direction)
  val q_2 = Lemma( Sequent( Seq( "GLB" -> GLB, "LUB" -> LUB, "R" -> R, "AS" -> AS ), Seq( "a" -> All( x, All( y, Eq( cap( cup( x, y ), x ), x ) ) ) ) ) ) {
    allR( x_0 )
    allR( y_0 )
    allL( cap( cup( x_0, y_0 ), x_0 ), "AS" )
    allL( x_0, "AS_0" )
    forget( "AS" )
    forget( "AS_0" )
    impL( "AS_0_0" )
    allL( cup( x_0, y_0 ), "GLB" )
    allL( x_0, "GLB_0" )
    forget( "GLB" )
    forget( "GLB_0" )
    andL( "GLB_0_0" )
    andR
    destruct( "GLB_0_0_0" )
    axiomLog
    insert( r_2 )
    axiomLog
  }

  // finishes r_1
  val r_1_1 = Lemma( Sequent( Seq( "GLB" -> GLB ), Seq( "a" -> leq( cap( x_0, y_0 ), x_0 ) ) ) ) {
    allL( x_0, "GLB" )
    allL( y_0, "GLB_0" )
    forget( "GLB" )
    forget( "GLB_0" )
    andL("GLB_0_0")
		andL("GLB_0_0_0")
		axiomLog
  }

  // absorption law 1 - difficult direction
	val r_1_a = All(z, Imp(And(leq(cap(x_0, y_0), z), leq(x_0, z)), leq(cup(cap(x_0, y_0), x_0), z)))
  val r_1 = Lemma( Sequent( Seq("a" -> r_1_a, "GLB" -> GLB, "R" -> R), Seq("b" -> leq(cup(cap(x_0, y_0), x_0), x_0)) ) ) {
    allL(x_0, "a")
		impL
		andR
		insert(r_1_1)
		allL(x_0, "R")
		eqR("R_0", "a_0").fromLeftToRight
		axiomRefl
		prop
  }

  // apply anti-symmetry to show absorption law 1 (+ easy direction)
  val q_1 = Lemma( Sequent( Seq("GLB" -> GLB, "LUB" -> LUB, "R" -> R, "AS" -> AS), Seq("a" -> All(x, All(y, Eq(cup(cap(x,y), x), x))))) ) {
    allR(x_0)
		allR(y_0)
		allL(cup(cap(x_0, y_0), x_0), "AS")
		allL(x_0, "AS_0")
		forget("AS")
		forget("AS_0")
		impL("AS_0_0")
		allL(cap(x_0, y_0), "LUB")
		allL(x_0, "LUB_0")
		forget("LUB")
		forget("LUB_0")
		andL("LUB_0_0")
		andL("LUB_0_0_0")
		andR
		insert(r_1)
		axiomLog
		axiomLog
  }

  val p3_2 = Lemma( Sequent( Seq("L3" -> L3), Seq("L2" -> L2) ) ) {
    repeat(andL)
		andR
		insert(q_1)
		insert(q_2)
  }

  // Main proof
  val p = Lemma( Sequent( Seq( "ax1" -> ax1, "ax2" -> ax2, "ax3" -> ax3, "ax4" -> ax4, "ax5" -> ax5, "ax6" -> ax6, "L1" -> L1 ), Seq( "L2" -> L2 ) ) ) {
    cut( L3, "L3" )
    insert( p1_3 )
    insert( p3_2 )
  }
}
