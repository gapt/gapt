package at.logic.testing

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.fol._

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._

import scala.collection.immutable.HashSet

import at.logic.language.lambda.substitutions._

// Functions to construct cut-free FOL LK proofs of the sequents
//
// P(0), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
//
// where n is an Integer parameter >= 0.

object LinearExampleProof
{
  val s = new ConstantStringSymbol("s")
  val p = new ConstantStringSymbol("P")
  val c = new ConstantStringSymbol("0")

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0)), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
  def proof( k: Int, n: Int )  : LKProof =
  {
    val x = FOLVar( VariableStringSymbol("x") )
    val ass = AllVar( x, Imp( Atom( p, x::Nil ), Atom( p, Function( s, x::Nil )::Nil ) ) )
    if ( k == n ) // leaf proof
    {
      val a = Atom( p,  Numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val p1 = Atom( p, Numeral( k )::Nil )
      val p2 = Atom( p, Numeral( k + 1 )::Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1::Nil, p1::Nil ), proof( k + 1, n ), p1, p2 ), aux, ass, Numeral( k ) ), ass )
    }
  }
}


// Functions to construct cut-free FOL LK proofs of the sequents
//
// P(0,0), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y. P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
//
// where n is an Integer parameter >= 0.
//
// The proofs constructed here go along the diagonal of P, i.e. one X-step, then one Y-step, etc.

object SquareDiagonalExampleProof
{
  val s = new ConstantStringSymbol("s")
  val p = new ConstantStringSymbol("P")
  val c = new ConstantStringSymbol("0")

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0),s^k(0)), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y . P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
  def proof( k: Int, n: Int )  : LKProof =
  {
    val x = FOLVar( VariableStringSymbol("x") )
    val y = FOLVar( VariableStringSymbol("y") )

    val assx = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, Function( s, x::Nil )::y::Nil ) ) ) )
    def assx_aux( k: Int ) = AllVar( y, Imp( Atom( p, Numeral( k )::y::Nil ), Atom(p, Numeral( k + 1 )::y::Nil ) ) )

    val assy = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, x::Function( s, y::Nil )::Nil ) ) ) )
    def assy_aux( k: Int ) = AllVar( y, Imp( Atom( p, Numeral( k )::y::Nil ), Atom(p, Numeral( k )::Function( s, y::Nil )::Nil ) ) )
 
    if ( k == n ) // leaf proof
    {
      val a = Atom( p, Numeral( n )::Numeral( n )::Nil )
      WeakeningLeftRule( WeakeningLeftRule( Axiom( a:: Nil, a::Nil ), assx ), assy )
    }
    else
    {
      val ayl = Atom( p, Numeral( k + 1 )::Numeral( k )::Nil ) // atom y left
      val ayr = Atom( p, Numeral( k + 1 )::Numeral( k + 1 )::Nil )
      val auxy = Imp( ayl, ayr )

      val p1 = ImpLeftRule( Axiom( ayl::Nil, ayl::Nil ), proof( k + 1, n), ayl, ayr )
      val p2 = ForallLeftRule( p1, auxy, assy_aux( k + 1 ), Numeral( k ) )
      val p3 = ForallLeftRule( p2, assy_aux( k + 1 ), assy, Numeral( k + 1) )
      val p4 = ContractionLeftRule( p3, assy )

      val axl = Atom( p, Numeral( k )::Numeral( k )::Nil ) // atom x left
      val axr = Atom( p, Numeral( k + 1 )::Numeral( k )::Nil )
      val auxx = Imp( axl, axr )

      val p5 = ImpLeftRule( Axiom( axl::Nil, axl::Nil ), p4, axl, axr )
      val p6 = ForallLeftRule( p5, auxx, assx_aux( k ), Numeral( k ) )
      val p7 = ForallLeftRule( p6, assx_aux( k ), assx, Numeral( k ) )
      ContractionLeftRule( p7, assx )
    }
  }
}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// P(0,0), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y. P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
//
// where n is an Integer parameter >= 0.
//
// The proofs constructed here go along the edges of P, i.e. first all X-steps are performed, then all Y-steps are performed

object SquareEdgesExampleProof
{
  val s = new ConstantStringSymbol("s")
  val p = new ConstantStringSymbol("P")
  val c = new ConstantStringSymbol("0")

  val x = FOLVar( VariableStringSymbol("x") )
  val y = FOLVar( VariableStringSymbol("y") )

  val assx = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, Function( s, x::Nil )::y::Nil ) ) ) )
  def assx_aux( k: Int ) = AllVar( y, Imp( Atom( p, Numeral( k )::y::Nil ), Atom(p, Numeral( k + 1 )::y::Nil ) ) )

  val assy = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, x::Function( s, y::Nil )::Nil ) ) ) )
  def assy_aux( k: Int ) = AllVar( y, Imp( Atom( p, Numeral( k )::y::Nil ), Atom(p, Numeral( k )::Function( s, y::Nil )::Nil ) ) )
 
  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0),0), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y. P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
  def proof( k: Int, n: Int ) : LKProof =
  {
    if ( k == n )
    {
      val p1 = ForallLeftRule( upper_proof( 0, n ), assy_aux( n ), assy, Numeral( n ) )
      WeakeningLeftRule( p1, assx )
    }
    else
    {
      val pk = Atom( p, Numeral( k )::Numeral( 0 )::Nil )
      val pkp1 = Atom( p, Numeral( k + 1 )::Numeral( 0 )::Nil )
      val impl = Imp( pk, pkp1 )

      ContractionLeftRule(
        ForallLeftRule(
          ForallLeftRule(
            ImpLeftRule(
              Axiom( pk::Nil, pk::Nil ),
              proof( k + 1, n ),
            pk, pkp1 ),
          impl, assx_aux( k ), Numeral( 0 )),
        assx_aux( k ), assx, Numeral( k )),
      assx )
    }
  }

  // returns LKProof with end-sequent  P(s^n(0),s^k(0)), \ALL y . P(s^n(0),y) -> P(s^n(0),s(y)) :- P(s^n(0),s^n(0))
  def upper_proof( k: Int, n: Int ) : LKProof =
  {
    if ( k == n ) // leaf proof
    {
      val a = Atom( p,  Numeral( n )::Numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), assy_aux( n ) )
    }
    else
    {
      val pk = Atom( p, Numeral( n )::Numeral( k )::Nil )
      val pkp1 = Atom( p, Numeral( n )::Numeral( k + 1 )::Nil )
      val impl = Imp( pk, pkp1 )

      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( pk::Nil, pk::Nil ), upper_proof( k + 1, n ), pk, pkp1 ), impl, assy_aux( n ), Numeral( k ) ), assy_aux( n ))
    }
  }
}

// Functions to construct the straightforward cut-free FOL LK proofs of the sequents
//
// P(s^n(0),0), \ALL x \ALL y . P(s(x),y) -> P(x,s(y)) :- P(0,s^n(0))
//
// where n is an Integer parameter >= 0.

object SumExampleProof
{
  val s = new ConstantStringSymbol("s")
  val p = new ConstantStringSymbol("P")

  val x = FOLVar( VariableStringSymbol("x") )
  val y = FOLVar( VariableStringSymbol("y") )

  val ass = AllVar( x, AllVar( y, Imp( Atom( p, Function( s, x::Nil )::y::Nil ), Atom( p, x::Function( s, y::Nil )::Nil ) ) ) )
  def ass_inst( x: Int ) = AllVar( y, Imp( Atom( p, Function( s, Numeral( x )::Nil )::y::Nil ), Atom( p, Numeral( x )::Function( s, y::Nil )::Nil ) ) )
  def ass_inst_inst( x: Int, y: Int ) = Imp( Atom( p, Function( s, Numeral( x )::Nil )::Numeral( y )::Nil ), Atom( p, Numeral( x )::Function( s, Numeral( y )::Nil )::Nil ) )

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^{n-k}(0),s^k(0)), \ALL x \ALL y. P(s(x),y) -> P(x,s(y)) :- P(0,s^n(0))
  def proof( k: Int, n: Int )  : LKProof =
  {
    if ( k == n ) // leaf proof
    {
      val a = Atom( p, Numeral( 0 )::Numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val a1 = Atom( p, Numeral( n - k )::Numeral( k )::Nil )
      val a2 = Atom( p, Numeral( n - (k + 1) )::Numeral( k + 1 )::Nil )

      ContractionLeftRule(
        ForallLeftRule(
          ForallLeftRule(
            ImpLeftRule(
              Axiom( a1::Nil, a1::Nil ),
              proof( k + 1, n ),
            a1, a2 ),
          ass_inst_inst( n - (k + 1), k ), ass_inst( n - (k + 1) ), Numeral( k ) ),
        ass_inst( n - (k + 1)), ass, Numeral( n - (k + 1) ) ),
      ass )
    }
  }
}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// Refl, Trans, \ALL x. f(x) = x :- f^n(a) = a
//
// where n is an Integer parameter >= 0.

object LinearEqExampleProof
{
  val a = new ConstantStringSymbol("a")
  val f = new ConstantStringSymbol("f")
  val eq = new ConstantStringSymbol("=")

  val x = FOLVar( VariableStringSymbol( "x" ))
  val y = FOLVar( VariableStringSymbol( "y" ))
  val z = FOLVar( VariableStringSymbol( "z" ))

  val Refl = AllVar( x, Atom( eq, x::x::Nil ))
  val Ass = AllVar( x, Atom( eq, Function( f, x::Nil )::x::Nil ))
  val Trans = AllVar( x, AllVar( y, AllVar( z, Imp( Atom( eq, x::y::Nil ), Imp( Atom( eq, y::z::Nil ), Atom( eq, x::z::Nil ) ) ) ) ) )

  def apply( n: Int ) = proof( n )

  // returns LKProof with end-sequent  Refl, Trans, \ALL x. f(x) = x :- f^k(a) = a
  def proof( k: Int )  : LKProof = {
    if ( k == 0 ) // leaf proof
    {
      val a_eq_a = Atom( eq, Iteration( a, f, 0 )::Iteration( a, f, 0 )::Nil )
      WeakeningLeftRule( WeakeningLeftRule( ForallLeftRule( Axiom( a_eq_a::Nil, a_eq_a::Nil ), a_eq_a, Refl, FOLConst( a ) ), Trans ), Ass )
    }
    else
    {
      // atoms
      val ka_eq_a = Atom( eq, Iteration( a, f, k )::Iteration( a, f, 0 )::Nil )
      val ka_eq_ka = Atom( eq, Iteration( a, f, k )::Iteration( a, f, k )::Nil )
      val kma_eq_a = Atom( eq, Iteration( a, f, k-1 )::Iteration( a, f, 0 )::Nil )
      val ka_eq_kma = Atom( eq, Iteration( a, f, k )::Iteration( a, f, k-1 )::Nil )
      val ka_eq_z = Atom( eq, Iteration( a, f, k )::z::Nil )
      val kma_eq_z = Atom( eq, Iteration( a, f, k-1 )::z::Nil )
      val y_eq_z = Atom( eq, y::z::Nil )
      val ka_eq_y = Atom( eq, Iteration( a, f, k )::y::Nil )
      val x_eq_y = Atom( eq, x::y::Nil )
      val x_eq_z = Atom( eq, x::z::Nil )
      
      // prop. formulas
      val Trans2 = Imp( kma_eq_a, ka_eq_a )
      val Trans3 = Imp( ka_eq_kma, Trans2 )

      // quant. formulas
      val Trans3_1 = AllVar( z, Imp( ka_eq_kma, Imp( kma_eq_z, ka_eq_z ) ) )
      val Trans3_2 = AllVar( y, AllVar( z, Imp( ka_eq_y, Imp( y_eq_z, ka_eq_z ) ) ) )
      val Trans3_3 = AllVar( x, AllVar( y, AllVar( z, Imp( x_eq_y, Imp( y_eq_z, x_eq_z ) ) ) ) )

      // prop. proofs
      val p1 = ImpLeftRule( proof( k-1 ), Axiom( ka_eq_a::Nil, ka_eq_a::Nil ), kma_eq_a, ka_eq_a )

      val p0 = Axiom( ka_eq_kma::Nil, ka_eq_kma::Nil )

      val p2 = ImpLeftRule( p0, p1, ka_eq_kma, Trans2 )

      // proofs containing quantifiers
      val p3 = ForallLeftRule( p2, Trans3, Trans3_1, Iteration( a, f, 0 ) )
      val p4 = ForallLeftRule( p3, Trans3_1, Trans3_2, Iteration( a, f, k-1 ) )
      val p5 = ForallLeftRule( p4, Trans3_2, Trans3_3, Iteration( a, f, k ) )

      val p6 = ForallLeftRule( p5, ka_eq_kma, Ass, Iteration( a, f, k-1 ) )
     
      val p7 = ContractionLeftRule( p6, Ass )
      val p8 = ContractionLeftRule( p7, Trans )

      p8
    }
  }
}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// Refl, Trans, CongSuc, ABase, ASuc, :- sum( n ) = s^n(0)
//
// where n is an Integer parameter >= 0.

object SumOfOnesExampleProof
{
  val eq = new ConstantStringSymbol("=")
  val s = new ConstantStringSymbol("s")
  val zero = new ConstantStringSymbol("0")
  val p = new ConstantStringSymbol("+")

  val x = FOLVar( VariableStringSymbol( "x" ))
  val y = FOLVar( VariableStringSymbol( "y" ))
  val z = FOLVar( VariableStringSymbol( "z" ))

  // axioms
  val Refl = AllVar( x, Atom( eq, x::x::Nil ))
  val Trans = AllVar( x, AllVar( y, AllVar( z, Imp( Atom( eq, x::y::Nil ), Imp( Atom( eq, y::z::Nil ), Atom( eq, x::z::Nil ) ) ) ) ) )
  val CongSuc = AllVar( x, AllVar( y, Imp( Atom( eq, x::y::Nil ), Atom( eq, Function( s, x::Nil )::Function( s, y::Nil )::Nil ) ) ) )
  val ABase = AllVar( x, Atom( eq, Function( p, x::FOLConst( zero )::Nil )::x::Nil ) )
  val ASuc = AllVar( x, AllVar( y, Atom( eq, Function( p, x::Function( s, y::Nil )::Nil )::Function( s, Function( p, x::y::Nil )::Nil )::Nil ) ) )

  def apply( n: Int ) = proof( n )

  private def proof( k: Int ) : LKProof = {
    if ( k == 0 )
    {
      val zero_eq_zero = Atom( eq, Numeral( 0 )::Numeral( 0 )::Nil )
      val p1 = ForallLeftRule( Axiom( zero_eq_zero::Nil, zero_eq_zero::Nil ), zero_eq_zero, Refl, Numeral( 0 ) )
      val p2 = WeakeningLeftRule( p1, Trans )
      val p3 = WeakeningLeftRule( p2, CongSuc )
      val p4 = WeakeningLeftRule( p3, ABase )
      WeakeningLeftRule( p4, ASuc )
    }
    else if ( k == 1 )
    {
      val one_eq_one = Atom( eq, Numeral( 1 )::Numeral( 1 )::Nil )
      val p1 = ForallLeftRule( Axiom( one_eq_one::Nil, one_eq_one::Nil ), one_eq_one, Refl, Numeral( 1 ) )
      val p2 = WeakeningLeftRule( p1, Trans )
      val p3 = WeakeningLeftRule( p2, CongSuc )
      val p4 = WeakeningLeftRule( p3, ABase )
      WeakeningLeftRule( p4, ASuc )
    }
    else
    {
      /// atoms
      val ssumkm1_eq_k = Atom( eq, Function( s, sum( k-1 )::Nil )::Numeral( k )::Nil )
      val ssumkm1_eq_z = Atom( eq, Function( s, sum( k-1 )::Nil )::z::Nil )
      val sumk_eq_k = Atom( eq, sum( k )::Numeral( k )::Nil )
      val sumk_eq_y = Atom( eq, sum( k )::y::Nil )
      val sumk_eq_z = Atom( eq, sum( k )::z::Nil )
      val y_eq_z = Atom( eq, y::z::Nil )
      val sumk_eq_ssumkm1 = Atom( eq, sum( k )::Function( s, sum( k-1 )::Nil )::Nil )
      val sumkm1_eq_km1 = Atom( eq, sum( k-1 )::Numeral( k-1 )::Nil )
      val sumkm1_eq_y = Atom( eq, sum( k-1 )::y::Nil )
      val ssumkm1_eq_sy = Atom( eq, Function( s, sum( k-1 )::Nil )::Function( s, y::Nil )::Nil )
      
      /// prop. formulas
      val Trans2 = Imp( ssumkm1_eq_k, sumk_eq_k )
      val Trans3 = Imp( sumk_eq_ssumkm1, Trans2 )
      val CongSuc2 = Imp( sumkm1_eq_km1, ssumkm1_eq_k )

      /// quant. formulas
      val Trans3_1 = AllVar( z, Imp( sumk_eq_ssumkm1, Imp( ssumkm1_eq_z, sumk_eq_z ) ) )
      val Trans3_2 = AllVar( y, AllVar( z, Imp( sumk_eq_y, Imp( y_eq_z, sumk_eq_z ) ) ) )
      val CongSuc2_1 = AllVar( y, Imp( sumkm1_eq_y, ssumkm1_eq_sy ) )

      /// proof
      // transitivity (using aux_proof)
      val p1 = Axiom( ssumkm1_eq_k::Nil, ssumkm1_eq_k::Nil )
      val p2 = Axiom( sumk_eq_k::Nil, sumk_eq_k::Nil )
      val p3 = ImpLeftRule( p1, p2, ssumkm1_eq_k, sumk_eq_k)
      val p4 = aux_proof( k-1 )
      val p5 = ImpLeftRule( p4, p3, sumk_eq_ssumkm1, Trans2 )
      val p6 = ForallLeftRule( p5, Trans3, Trans3_1, Numeral( k ) )
      val p7 = ForallLeftRule( p6, Trans3_1, Trans3_2, Function( s, sum( k-1 )::Nil ) )
      val p8 = ForallLeftRule( p7, Trans3_2, Trans, sum( k ) )
      val p9 = ContractionLeftRule( p8, Trans )

      // congruence sucessor (using IH)
      val p10 = proof( k-1 )
      val p11 = ImpLeftRule( p10, p9, sumkm1_eq_km1, ssumkm1_eq_k )
      val p12 = ContractionLeftRule( p11, Trans )
      val p13 = ContractionLeftRule( p12, CongSuc )
      val p14 = ContractionLeftRule( p13, ASuc )
      val p15 = ContractionLeftRule( p14, ABase )
      val p16 = ForallLeftRule( p15, CongSuc2, CongSuc2_1, Numeral( k-1 ) )
      val p17 = ForallLeftRule( p16, CongSuc2_1, CongSuc, sum( k-1 ) )
      ContractionLeftRule( p17, CongSuc )
    }
  }

  // constructs proof of: Trans, CongSuc, ASuc, ABase :- sum( k + 1 ) = s( sum( k ) )
  private def aux_proof( k: Int ) : LKProof = {
    /// atoms
    val ssumkp0_eq_ssumk = Atom( eq, Function( s, Function( p, sum( k )::Numeral( 0 )::Nil )::Nil )::Function( s, sum( k )::Nil )::Nil )
    val sumkp1_eq_ssumk = Atom( eq, sum( k+1 )::Function( s, sum( k )::Nil )::Nil )
    val sumkp1_eq_ssumkp0 = Atom( eq, sum( k+1 )::Function( s, Function( p, sum( k )::Numeral( 0 )::Nil )::Nil )::Nil )
    val ssumkp0_eq_z = Atom( eq, Function( s, Function( p, sum( k )::Numeral( 0 )::Nil )::Nil )::z::Nil )
    val sumkp1_eq_z = Atom( eq, sum( k+1 )::z::Nil )
    val sumkp1_eq_y = Atom( eq, sum( k+1 )::y::Nil )
    val y_eq_z = Atom( eq, y::z::Nil )
    val sumkp0_eq_sumk = Atom( eq, Function( p, sum( k )::Numeral( 0 )::Nil )::sum( k )::Nil )
    val sumkp0_eq_y = Atom( eq, Function( p, sum( k )::Numeral( 0 )::Nil )::y::Nil )
    val ssumkp0_eq_sy = Atom( eq, Function( s, Function( p, sum( k )::Numeral( 0 )::Nil )::Nil )::Function( s, y::Nil )::Nil )
    val sumkpsy_eq_ssumkpy = Atom( eq, Function( p, sum( k )::Function( s, y::Nil)::Nil )::Function( s, Function( p, sum( k )::y::Nil )::Nil )::Nil )
 
    /// prop. formulas
    val Trans2 = Imp( ssumkp0_eq_ssumk, sumkp1_eq_ssumk )
    val Trans3 = Imp( sumkp1_eq_ssumkp0, Trans2 )
    val Cong2 = Imp( sumkp0_eq_sumk, ssumkp0_eq_ssumk )

    /// quant. formulas
    val Trans3_1 = AllVar( z, Imp( sumkp1_eq_ssumkp0, Imp( ssumkp0_eq_z, sumkp1_eq_z ) ) )
    val Trans3_2 = AllVar( y, AllVar( z, Imp( sumkp1_eq_y, Imp( y_eq_z, sumkp1_eq_z ) ) ) )
    val Cong2_1 = AllVar( y, Imp( sumkp0_eq_y, ssumkp0_eq_sy ) )
    val ASuc_1 = AllVar( y, sumkpsy_eq_ssumkpy )

    /// proof
    // transitivity
    val p1 = Axiom( ssumkp0_eq_ssumk::Nil, ssumkp0_eq_ssumk::Nil )
    val p2 = Axiom( sumkp1_eq_ssumk::Nil, sumkp1_eq_ssumk::Nil )
    val p3 = ImpLeftRule( p1, p2, ssumkp0_eq_ssumk, sumkp1_eq_ssumk )
    val p4 = Axiom( sumkp1_eq_ssumkp0::Nil, sumkp1_eq_ssumkp0::Nil )
    val p5 = ImpLeftRule( p4, p3, sumkp1_eq_ssumkp0, Trans2 )
    val p6 = ForallLeftRule( p5, Trans3, Trans3_1, Function( s, sum( k )::Nil ) )
    val p7 = ForallLeftRule( p6, Trans3_1, Trans3_2, Function( s, Function( p, sum( k )::Numeral( 0 )::Nil )::Nil ) )
    val p8 = ForallLeftRule( p7, Trans3_2, Trans, sum( k+1 ) )

    // congruence sucessor
    val p9 = Axiom( sumkp0_eq_sumk::Nil, sumkp0_eq_sumk::Nil )
    val p10 = ImpLeftRule( p9, p8, sumkp0_eq_sumk, ssumkp0_eq_ssumk )
    val p11 = ForallLeftRule( p10, Cong2, Cong2_1, sum( k ) )
    val p12 = ForallLeftRule( p11, Cong2_1, CongSuc, Function( p, sum( k )::Numeral( 0 )::Nil ) )

    // addition sucessor case
    val p13 = ForallLeftRule( p12, sumkp1_eq_ssumkp0, ASuc_1, Numeral( 0 ) )
    val p14 = ForallLeftRule( p13, ASuc_1, ASuc, sum( k ) )

    // addition base case
    ForallLeftRule( p14, sumkp0_eq_sumk, ABase, sum( k ) )
  }

  // the term (.((1 + 1) + 1 ) + ... + 1 ), k must be at least 1
  private def sum( k: Int ) : FOLTerm = {
    if ( k == 1 )  Numeral( 1 )
    else           Function( p, sum( k-1 )::Numeral( 1 )::Nil )
  }
}




// Constructs the set of FOLTerms { 0, s(0), s(s(0)), ..., s^n(0) }

object LinearExampleTermset
{ 
  def apply( n: Int ) : List[FOLTerm] =
    if ( n == 0 )
      List[FOLTerm]()
    else
      Numeral( n - 1 ) :: apply( n - 1)
}


// constructs the FOLTerm s^k(0)
object Numeral
{
  val z = new ConstantStringSymbol( "0" )
  val s = new ConstantStringSymbol( "s" )
  
  def apply( k: Int ) = Iteration.apply( z, s, k )
}

// contructs the FOLTerm f^k(a)
object Iteration
{
  def apply( a: ConstantStringSymbol, f: ConstantStringSymbol, k: Int ) : FOLTerm =
    if ( k == 0 ) FOLConst( a ) else Function( f, apply( a, f, k-1 )::Nil )
}

// Workaround until there is a real FOLSubstitution
// applies a substitution x <- t to a formula or term f
/*
object FOLSubstitution
{

    def apply(f: FOLFormula, x: FOLVar, t: FOLTerm) : FOLFormula = 
    {
      val sub = Substitution(x, t.asInstanceOf[FOLExpression])
      sub( f.asInstanceOf[FOLExpression] ).asInstanceOf[FOLFormula]
    }

    def apply(f: FOLTerm, x: FOLVar, t: FOLTerm) : FOLTerm =
    {
      val sub = Substitution(x, t.asInstanceOf[FOLExpression])
      sub( f.asInstanceOf[FOLExpression] ).asInstanceOf[FOLTerm]
    }
}
*/
