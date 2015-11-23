package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLSubstitution, Utils }
import at.logic.gapt.expr.hol.{ univclosure, instantiate }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.proofs.lkNew._

trait ProofSequence {
  def apply( n: Int ): LKProof

  def name = getClass.getSimpleName.replace( "$", "" )
}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// P(0), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
//
// where n is an Integer parameter >= 0.
object LinearExampleProof extends ProofSequence {
  val s = "s"
  val p = "P"
  val c = "0"

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0)), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
  def proof( k: Int, n: Int ): LKProof =
    {
      val x = FOLVar( "x" )
      val ass = All( x, Imp( FOLAtom( p, x :: Nil ), FOLAtom( p, FOLFunction( s, x :: Nil ) :: Nil ) ) )
      if ( k == n ) // leaf proof
      {
        val a = FOLAtom( p, Utils.numeral( n ) :: Nil )
        WeakeningLeftRule( LogicalAxiom( a ), ass )
      } else {
        val p1 = FOLAtom( p, Utils.numeral( k ) :: Nil )
        val p2 = FOLAtom( p, Utils.numeral( k + 1 ) :: Nil )
        val aux = Imp( p1, p2 )
        ContractionLeftRule( ForallLeftRule( ImpLeftRule( LogicalAxiom( p1 ), p1, proof( k + 1, n ), p2 ), ass, Utils.numeral( k ) ), ass )
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
object SquareDiagonalExampleProof extends ProofSequence {
  val s = "s"
  val p = "P"
  val c = "0"

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0),s^k(0)), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y . P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
  def proof( k: Int, n: Int ): LKProof =
    {
      val x = FOLVar( "x" )
      val y = FOLVar( "y" )

      val assx = All( x, All( y, Imp( FOLAtom( p, x :: y :: Nil ), FOLAtom( p, FOLFunction( s, x :: Nil ) :: y :: Nil ) ) ) )
      def assx_aux( k: Int ) = All( y, Imp( FOLAtom( p, Utils.numeral( k ) :: y :: Nil ), FOLAtom( p, Utils.numeral( k + 1 ) :: y :: Nil ) ) )

      val assy = All( x, All( y, Imp( FOLAtom( p, x :: y :: Nil ), FOLAtom( p, x :: FOLFunction( s, y :: Nil ) :: Nil ) ) ) )
      def assy_aux( k: Int ) = All( y, Imp( FOLAtom( p, Utils.numeral( k ) :: y :: Nil ), FOLAtom( p, Utils.numeral( k ) :: FOLFunction( s, y :: Nil ) :: Nil ) ) )

      if ( k == n ) // leaf proof
      {
        val a = FOLAtom( p, Utils.numeral( n ) :: Utils.numeral( n ) :: Nil )
        WeakeningLeftRule( WeakeningLeftRule( LogicalAxiom( a ), assx ), assy )
      } else {
        val ayl = FOLAtom( p, Utils.numeral( k + 1 ) :: Utils.numeral( k ) :: Nil ) // atom y left
        val ayr = FOLAtom( p, Utils.numeral( k + 1 ) :: Utils.numeral( k + 1 ) :: Nil )
        val auxy = Imp( ayl, ayr )

        val p1 = ImpLeftRule( LogicalAxiom( ayl ), ayl, proof( k + 1, n ), ayr )
        val p2 = ForallLeftRule( p1, assy_aux( k + 1 ), Utils.numeral( k ) )
        val p3 = ForallLeftRule( p2, assy, Utils.numeral( k + 1 ) )
        val p4 = ContractionLeftRule( p3, assy )

        val axl = FOLAtom( p, Utils.numeral( k ) :: Utils.numeral( k ) :: Nil ) // atom x left
        val axr = FOLAtom( p, Utils.numeral( k + 1 ) :: Utils.numeral( k ) :: Nil )
        val auxx = Imp( axl, axr )

        val p5 = ImpLeftRule( LogicalAxiom( axl ), axl, p4, axr )
        val p6 = ForallLeftRule( p5, assx_aux( k ), Utils.numeral( k ) )
        val p7 = ForallLeftRule( p6, assx, Utils.numeral( k ) )
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
object SquareEdgesExampleProof extends ProofSequence {
  val s = "s"
  val p = "P"
  val c = "0"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  val assx = All( x, All( y, Imp( FOLAtom( p, x :: y :: Nil ), FOLAtom( p, FOLFunction( s, x :: Nil ) :: y :: Nil ) ) ) )
  def assx_aux( k: Int ) = All( y, Imp( FOLAtom( p, Utils.numeral( k ) :: y :: Nil ), FOLAtom( p, Utils.numeral( k + 1 ) :: y :: Nil ) ) )

  val assy = All( x, All( y, Imp( FOLAtom( p, x :: y :: Nil ), FOLAtom( p, x :: FOLFunction( s, y :: Nil ) :: Nil ) ) ) )
  def assy_aux( k: Int ) = All( y, Imp( FOLAtom( p, Utils.numeral( k ) :: y :: Nil ), FOLAtom( p, Utils.numeral( k ) :: FOLFunction( s, y :: Nil ) :: Nil ) ) )

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0),0), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y. P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
  def proof( k: Int, n: Int ): LKProof =
    {
      if ( k == n ) {
        val p1 = ForallLeftRule( upper_proof( 0, n ), assy, Utils.numeral( n ) )
        WeakeningLeftRule( p1, assx )
      } else {
        val pk = FOLAtom( p, Utils.numeral( k ) :: Utils.numeral( 0 ) :: Nil )
        val pkp1 = FOLAtom( p, Utils.numeral( k + 1 ) :: Utils.numeral( 0 ) :: Nil )
        val impl = Imp( pk, pkp1 )

        ContractionLeftRule(
          ForallLeftRule(
            ForallLeftRule(
              ImpLeftRule(
                Axiom( pk :: Nil, pk :: Nil ), pk,
                proof( k + 1, n ), pkp1
              ),
              assx_aux( k ), Utils.numeral( 0 )
            ),
            assx, Utils.numeral( k )
          ),
          assx
        )
      }
    }

  // returns LKProof with end-sequent  P(s^n(0),s^k(0)), \ALL y . P(s^n(0),y) -> P(s^n(0),s(y)) :- P(s^n(0),s^n(0))
  def upper_proof( k: Int, n: Int ): LKProof =
    {
      if ( k == n ) // leaf proof
      {
        val a = FOLAtom( p, Utils.numeral( n ) :: Utils.numeral( n ) :: Nil )
        WeakeningLeftRule( LogicalAxiom( a ), assy_aux( n ) )
      } else {
        val pk = FOLAtom( p, Utils.numeral( n ) :: Utils.numeral( k ) :: Nil )
        val pkp1 = FOLAtom( p, Utils.numeral( n ) :: Utils.numeral( k + 1 ) :: Nil )
        val impl = Imp( pk, pkp1 )

        ContractionLeftRule( ForallLeftRule( ImpLeftRule( LogicalAxiom( pk ), pk, upper_proof( k + 1, n ), pkp1 ), assy_aux( n ), Utils.numeral( k ) ), assy_aux( n ) )
      }
    }
}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// P(a,b), \ALL x \ALL y. P(x,y) -> P(sx(x),y), \ALL x \ALL y. P(x,y) -> P(x,sx(y)) :- P(sx^n(a),sy^n(b))
//
// where n is an Integer parameter >= 0.
//
// The proofs constructed here go along the edges of P, i.e. first all X-steps are performed, then all Y-steps are performed,
// but unlike SquareEdgesExampleProof, different functions are used for the X- and the Y-directions.
object SquareEdges2DimExampleProof extends ProofSequence {
  //separate sucessor for the x- and y-directions
  val sx = "s_x"
  val sy = "s_y"
  //0 of the x-axis
  val a = "a"
  //0 of the y-axis
  val b = "b"

  val p = "P"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  //Converts integers into terms consisting of nested application of the successor function to 0
  def numeralX( n: Int ) = Utils.iterateTerm( FOLConst( a ), sx, n )
  def numeralY( n: Int ) = Utils.iterateTerm( FOLConst( b ), sy, n )

  val assx = All( x, All( y, Imp( FOLAtom( p, x :: y :: Nil ), FOLAtom( p, FOLFunction( sx, x :: Nil ) :: y :: Nil ) ) ) )
  def assx_aux( k: Int ) = All( y, Imp( FOLAtom( p, numeralX( k ) :: y :: Nil ), FOLAtom( p, numeralX( k + 1 ) :: y :: Nil ) ) )

  val assy = All( x, All( y, Imp( FOLAtom( p, x :: y :: Nil ), FOLAtom( p, x :: FOLFunction( sy, y :: Nil ) :: Nil ) ) ) )
  def assy_aux( k: Int ) = All( y, Imp( FOLAtom( p, numeralX( k ) :: y :: Nil ), FOLAtom( p, numeralX( k ) :: FOLFunction( sy, y :: Nil ) :: Nil ) ) )

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(sx^k(a),0), \ALL x \ALL y. P(x,y) -> P(sx(x),y), \ALL x \ALL y. P(x,y) -> P(x,sy(y)) :- P(sx^n(a),sy^n(b))
  def proof( k: Int, n: Int ): LKProof =
    {
      if ( k == n ) {
        val p1 = ForallLeftRule( upper_proof( 0, n ), assy, numeralX( n ) )
        WeakeningLeftRule( p1, assx )
      } else {
        val pk = FOLAtom( p, numeralX( k ) :: numeralY( 0 ) :: Nil )
        val pkp1 = FOLAtom( p, numeralX( k + 1 ) :: numeralY( 0 ) :: Nil )
        val impl = Imp( pk, pkp1 )

        ContractionLeftRule(
          ForallLeftRule(
            ForallLeftRule(
              ImpLeftRule(
                LogicalAxiom( pk ), pk,
                proof( k + 1, n ), pkp1
              ),
              assx_aux( k ), numeralY( 0 )
            ), //possibly not correct -> switch?
            assx, numeralX( k )
          ), //same
          assx
        )
      }
    }

  // returns LKProof with end-sequent  P(s^n(0),s^k(0)), \ALL y . P(s^n(0),y) -> P(s^n(0),s(y)) :- P(s^n(0),s^n(0))
  //Conjecture: this is the part that goes in the Y-direction.
  def upper_proof( k: Int, n: Int ): LKProof =
    {
      if ( k == n ) // leaf proof
      {
        val ax = FOLAtom( p, numeralX( n ) :: numeralY( n ) :: Nil )
        WeakeningLeftRule( Axiom( ax :: Nil, ax :: Nil ), assy_aux( n ) )
      } else {
        val pk = FOLAtom( p, numeralX( n ) :: numeralY( k ) :: Nil )
        val pkp1 = FOLAtom( p, numeralX( n ) :: numeralY( k + 1 ) :: Nil )
        val impl = Imp( pk, pkp1 )

        ContractionLeftRule(
          ForallLeftRule(
            ImpLeftRule(
              LogicalAxiom( pk ),
              pk,
              upper_proof( k + 1, n ),
              pkp1
            ),
            assy_aux( n ),
            numeralY( k )
          ), //possibly not correct: switch or maybe restructure.
          assy_aux( n )
        )
      }
    }
}

// Functions to construct the straightforward cut-free FOL LK proofs of the sequents
//
// P(s^n(0),0), \ALL x \ALL y . P(s(x),y) -> P(x,s(y)) :- P(0,s^n(0))
//
// where n is an Integer parameter >= 0.
object SumExampleProof extends ProofSequence {
  val s = "s"
  val p = "P"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  val ass = All( x, All( y, Imp( FOLAtom( p, FOLFunction( s, x :: Nil ) :: y :: Nil ), FOLAtom( p, x :: FOLFunction( s, y :: Nil ) :: Nil ) ) ) )
  def ass_inst( x: Int ) = All( y, Imp( FOLAtom( p, FOLFunction( s, Utils.numeral( x ) :: Nil ) :: y :: Nil ), FOLAtom( p, Utils.numeral( x ) :: FOLFunction( s, y :: Nil ) :: Nil ) ) )
  def ass_inst_inst( x: Int, y: Int ) = Imp( FOLAtom( p, FOLFunction( s, Utils.numeral( x ) :: Nil ) :: Utils.numeral( y ) :: Nil ), FOLAtom( p, Utils.numeral( x ) :: FOLFunction( s, Utils.numeral( y ) :: Nil ) :: Nil ) )

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^{n-k}(0),s^k(0)), \ALL x \ALL y. P(s(x),y) -> P(x,s(y)) :- P(0,s^n(0))
  def proof( k: Int, n: Int ): LKProof =
    {
      if ( k == n ) // leaf proof
      {
        val a = FOLAtom( p, Utils.numeral( 0 ) :: Utils.numeral( n ) :: Nil )
        WeakeningLeftRule( LogicalAxiom( a ), ass )
      } else {
        val a1 = FOLAtom( p, Utils.numeral( n - k ) :: Utils.numeral( k ) :: Nil )
        val a2 = FOLAtom( p, Utils.numeral( n - ( k + 1 ) ) :: Utils.numeral( k + 1 ) :: Nil )

        ContractionLeftRule(
          ForallLeftRule(
            ForallLeftRule(
              ImpLeftRule(
                LogicalAxiom( a1 ),
                a1,
                proof( k + 1, n ),
                a2
              ),
              ass_inst( n - ( k + 1 ) ), Utils.numeral( k )
            ),
            ass, Utils.numeral( n - ( k + 1 ) )
          ),
          ass
        )
      }
    }
}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// Refl, Trans, \ALL x. f(x) = x :- f^n(a) = a
//
// where n is an Integer parameter >= 0.
object LinearEqExampleProof extends ProofSequence {
  val a = "a"
  val f = "f"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  val Refl = All( x, Eq( x, x ) )
  val Ass = All( x, Eq( FOLFunction( f, x :: Nil ), x ) )
  val Trans = All( x, All( y, All( z, Imp( Eq( x, y ), Imp( Eq( y, z ), Eq( x, z ) ) ) ) ) )

  def apply( n: Int ) = proof( n )

  // returns LKProof with end-sequent  Refl, Trans, \ALL x. f(x) = x :- f^k(a) = a
  def proof( k: Int ): LKProof = {
    if ( k == 0 ) // leaf proof
    {
      val a_eq_a = Eq( Utils.iterateTerm( FOLConst( a ), f, 0 ), Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      WeakeningLeftRule( WeakeningLeftRule( ForallLeftRule( LogicalAxiom( a_eq_a ), Refl, FOLConst( a ) ), Trans ), Ass )
    } else {
      // atoms
      val ka_eq_a = Eq( Utils.iterateTerm( FOLConst( a ), f, k ), Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      val ka_eq_ka = Eq( Utils.iterateTerm( FOLConst( a ), f, k ), Utils.iterateTerm( FOLConst( a ), f, k ) )
      val kma_eq_a = Eq( Utils.iterateTerm( FOLConst( a ), f, k - 1 ), Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      val ka_eq_kma = Eq( Utils.iterateTerm( FOLConst( a ), f, k ), Utils.iterateTerm( FOLConst( a ), f, k - 1 ) )
      val ka_eq_z = Eq( Utils.iterateTerm( FOLConst( a ), f, k ), z )
      val kma_eq_z = Eq( Utils.iterateTerm( FOLConst( a ), f, k - 1 ), z )
      val y_eq_z = Eq( y, z )
      val ka_eq_y = Eq( Utils.iterateTerm( FOLConst( a ), f, k ), y )
      val x_eq_y = Eq( x, y )
      val x_eq_z = Eq( x, z )

      // prop. formulas
      val Trans2 = Imp( kma_eq_a, ka_eq_a )
      val Trans3 = Imp( ka_eq_kma, Trans2 )

      // quant. formulas
      val Trans3_1 = All( z, Imp( ka_eq_kma, Imp( kma_eq_z, ka_eq_z ) ) )
      val Trans3_2 = All( y, All( z, Imp( ka_eq_y, Imp( y_eq_z, ka_eq_z ) ) ) )
      val Trans3_3 = All( x, All( y, All( z, Imp( x_eq_y, Imp( y_eq_z, x_eq_z ) ) ) ) )

      // prop. proofs
      val p1 = ImpLeftRule( proof( k - 1 ), kma_eq_a, Axiom( ka_eq_a :: Nil, ka_eq_a :: Nil ), ka_eq_a )

      val p0 = LogicalAxiom( ka_eq_kma )

      val p2 = ImpLeftRule( p0, ka_eq_kma, p1, Trans2 )

      // proofs containing quantifiers
      val p3 = ForallLeftRule( p2, Trans3_1, Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      val p4 = ForallLeftRule( p3, Trans3_2, Utils.iterateTerm( FOLConst( a ), f, k - 1 ) )
      val p5 = ForallLeftRule( p4, Trans3_3, Utils.iterateTerm( FOLConst( a ), f, k ) )

      val p6 = ForallLeftRule( p5, Ass, Utils.iterateTerm( FOLConst( a ), f, k - 1 ) )

      val p7 = ContractionLeftRule( p6, Ass )
      val p8 = ContractionLeftRule( p7, Trans )

      p8
    }
  }
}

object SumOfOnesF2ExampleProof extends ProofSequence {
  val s = "s"
  val zero = "0"
  val p = "+"
  var f = "f"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  //Helpers
  def Fn( n: Int ) = FOLFunction( f, Utils.numeral( n ) :: Nil )

  //Forall x.(x + 1 = s(x)) (reversed to avoid the application of the symmetry of =)
  val Plus = All( x, Eq( FOLFunction( p, x :: Utils.numeral( 1 ) :: Nil ), FOLFunction( s, x :: Nil ) ) )
  def PlusX( x: FOLTerm ) = Eq( FOLFunction( p, x :: Utils.numeral( 1 ) :: Nil ), FOLFunction( s, x :: Nil ) )

  //Forall xyz.(y=z -> (x+y=x+z))
  val EqPlus = All( x, All( y, All( z, Imp( Eq( y, z ), Eq( FOLFunction( p, y :: x :: Nil ), FOLFunction( p, z :: x :: Nil ) ) ) ) ) )
  def EqPlusX( x: FOLTerm ) = All( y, All( z, Imp( Eq( y, z ), Eq( FOLFunction( p, y :: x :: Nil ), FOLFunction( p, z :: x :: Nil ) ) ) ) )
  def EqPlusXY( x: FOLTerm, y: FOLTerm ) = All( z, Imp( Eq( y, z ), Eq( FOLFunction( p, y :: x :: Nil ), FOLFunction( p, z :: x :: Nil ) ) ) )
  def EqPlusXYZ( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Imp( Eq( y, z ), Eq( FOLFunction( p, y :: x :: Nil ), FOLFunction( p, z :: x :: Nil ) ) )

  //Forall xyz.(x = y ^ y = z -> x = z)
  val Trans = All( x, All( y, All( z, Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) ) ) ) )

  //Definition of f
  //f(0) = 0
  val FZero = Eq( FOLFunction( f, Utils.numeral( 0 ) :: Nil ), Utils.numeral( 0 ) )
  //Forall x.f(s(x)) = f(x) + s(0)
  val FSucc = All( x, Eq( FOLFunction( f, FOLFunction( s, x :: Nil ) :: Nil ), FOLFunction( p, FOLFunction( f, x :: Nil ) :: Utils.numeral( 1 ) :: Nil ) ) )
  def FSuccX( x: FOLTerm ) = Eq( FOLFunction( f, FOLFunction( s, x :: Nil ) :: Nil ), FOLFunction( p, FOLFunction( f, x :: Nil ) :: Utils.numeral( 1 ) :: Nil ) )

  //The starting axiom f(n) = n |- f(n) = n
  def start( n: Int ) =
    WeakeningMacroRule(
      LogicalAxiom( Fn( n ) === Utils.numeral( n ) ),
      Eq( Fn( n ), Utils.numeral( n ) ) +: Trans +: Plus +: EqPlus +: FSucc +: Sequent() :+ Eq( Fn( n ), Utils.numeral( n ) )
    )

  def apply( n: Int ) = RecProof( start( n ), n )

  /**
   * Recursively constructs the proof, starting with the proof s1.
   */
  def RecProof( s1: LKProof, n: Int ): LKProof = {
    if ( n <= 0 ) { s1 }
    else {

      val fn_eq_n = Eq( Fn( n - 1 ), Utils.numeral( n - 1 ) )
      val fn_s0 = FOLFunction( p, Fn( n - 1 ) :: Utils.numeral( 1 ) :: Nil )
      val n_s0 = FOLFunction( p, Utils.numeral( n - 1 ) :: Utils.numeral( 1 ) :: Nil )

      val tr = TransRule( Fn( n ), n_s0, Utils.numeral( n ), s1 )

      val tr2 = TransRule( Fn( n ), fn_s0, n_s0, tr )

      val impl = ImpLeftRule( LogicalAxiom( fn_eq_n ), fn_eq_n, tr2, Eq( fn_s0, n_s0 ) )

      //Instantiate FSucc
      val allQFSucc = ForallLeftRule( impl, FSucc, Utils.numeral( n - 1 ) )
      val clFSucc = ContractionLeftRule( allQFSucc, FSucc )

      //Instantiate Plus
      val allQPlus = ForallLeftRule( clFSucc, Plus, Utils.numeral( n - 1 ) )
      val clPlus = ContractionLeftRule( allQPlus, Plus )

      //Instantiare EqPlus (x=(s0), y=Fn(n-1), z=n-1)
      val eqx = Utils.numeral( 1 )
      val eqy = Fn( n - 1 )
      val eqz = Utils.numeral( n - 1 )

      val allQEqPlusZ = ForallLeftRule( clPlus, EqPlusXY( eqx, eqy ), eqz )
      val allQEqPlusYZ = ForallLeftRule( allQEqPlusZ, EqPlusX( eqx ), eqy )
      val allQEqPlusXYZ = ForallLeftRule( allQEqPlusYZ, EqPlus, eqx )
      val clEqPlus = ContractionLeftRule( allQEqPlusXYZ, EqPlus )

      RecProof( clEqPlus, n - 1 )
    }
  }
}

/**
 * Constructs the cut-free FOL LK proof of the sequent
 *
 * AUX, f(0) = 0, Forall x.f(s(x)) = f(x) + s(0) |- f(s^n(0)) = s^n(0)
 * Where AUX is {Transitivity, Symmetry, Reflexity of =,
 *               Forall xy.x=y -> s(x) = s(y), f(0) = 0, Forall x.f(s(x)) = f(x) + s(0)}
 */
object SumOfOnesFExampleProof extends ProofSequence {
  val s = "s"
  val zero = "0"
  val p = "+"
  var f = "f"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  //Helpers
  def Fn( n: Int ) = FOLFunction( f, Utils.numeral( n ) :: Nil )

  //Forall xyz.(x = y ^ y = z -> x = z)
  val Trans = All( x, All( y, All( z, Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) ) ) ) )

  //Forall xy.(x=y -> s(x) = s(y))
  val CongSucc = All( x, All( y, Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) ) ) )
  def CongSuccX( x: FOLTerm ) = All( y, Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) ) )
  def CongSuccXY( x: FOLTerm, y: FOLTerm ) = Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) )

  //Forall x.(x + 1 = s(x)) (reversed to avoid the application of the symmetry of =)
  val Plus = All( x, Eq( FOLFunction( p, x :: Utils.numeral( 1 ) :: Nil ), FOLFunction( s, x :: Nil ) ) )
  def PlusX( x: FOLTerm ) = Eq( FOLFunction( p, x :: Utils.numeral( 1 ) :: Nil ), FOLFunction( s, x :: Nil ) )

  //Definition of f
  //f(0) = 0
  val FZero = Eq( FOLFunction( f, Utils.numeral( 0 ) :: Nil ), Utils.numeral( 0 ) )
  //Forall x.f(s(x)) = f(x) + s(0)
  val FSucc = All( x, Eq( FOLFunction( f, FOLFunction( s, x :: Nil ) :: Nil ), FOLFunction( p, FOLFunction( f, x :: Nil ) :: Utils.numeral( 1 ) :: Nil ) ) )
  def FSuccX( x: FOLTerm ) = Eq( FOLFunction( f, FOLFunction( s, x :: Nil ) :: Nil ), FOLFunction( p, FOLFunction( f, x :: Nil ) :: Utils.numeral( 1 ) :: Nil ) )

  //The starting axiom f(n) = n |- f(n) = n
  def start( n: Int ) =
    WeakeningMacroRule(
      LogicalAxiom( Fn( n ) === Utils.numeral( n ) ),
      Eq( Fn( n ), Utils.numeral( n ) ) +: Trans +: Plus +: CongSucc +: FSucc +: Sequent() :+ Eq( Fn( n ), Utils.numeral( n ) )
    )

  def apply( n: Int ) = proof( n )
  def proof( n: Int ) = TermGenProof( EqChainProof( start( n ), n ), 0, n )

  /**
   * Generates a sequent containing, in addition to the formulas in the bottommost sequent of s1,
   * the chain of equations f(n) = s(f(n-1)),...,f(1)=s(f(0)), f(0) = 0.s
   * The generates proof employs only the axiom of transitivity and (x=y -> s(x) = s(y)))
   *
   * TODO should be private - but scala shell does not allow access modifiers when :loading a file
   */
  def EqChainProof( s1: LKProof, n: Int ): LKProof = {
    if ( n <= 0 ) { s1 }
    else {
      val tr = TransRule( Fn( n ), Utils.iterateTerm( Fn( n - 1 ), s, 1 ), Utils.numeral( n ), s1 )

      val ax2 = LogicalAxiom( Eq( Fn( n - 1 ), Utils.numeral( n - 1 ) ) )

      //Introduces the instantiated form of CongSuc
      val impl = ImpLeftRule( ax2, Eq( Fn( n - 1 ), Utils.numeral( n - 1 ) ), tr, Eq( Utils.iterateTerm( Fn( n - 1 ), s, 1 ), Utils.numeral( n ) ) )

      //Quantify CongSucc
      val cong1 = ForallLeftRule( impl, CongSuccX( Fn( n - 1 ) ), Utils.numeral( n - 1 ) )
      val cong2 = ForallLeftRule( cong1, CongSucc, Fn( n - 1 ) )

      val cl = ContractionLeftRule( cong2, CongSucc )

      EqChainProof( cl, n - 1 )
    }
  }

  /**
   * Given a proof s1, produced by EqChainProof, generates a proof that
   * eliminates the chains of equasions and proves the final sequent
   * FZero, FSucc, TR, Plus |- f(n) = n.
   *
   * TODO should be private - but scala shell does not allow access modifiers when :loading a file
   */
  def TermGenProof( s1: LKProof, n: Int, targetN: Int ): LKProof = {
    if ( n >= targetN ) { s1 }
    else {

      val tr = TransRule( Fn( n + 1 ), FOLFunction( p, Fn( n ) :: Utils.numeral( 1 ) :: Nil ), Utils.iterateTerm( Fn( n ), s, 1 ), s1 )

      //Quantify plus
      val plus = ForallLeftRule( tr, Plus, Fn( n ) )
      val clPlus = ContractionLeftRule( plus, Plus )

      //Quantify fsucc
      val fsucc = ForallLeftRule( clPlus, FSucc, Utils.numeral( n ) )
      val clFSucc = ContractionLeftRule( fsucc, FSucc )

      TermGenProof( clFSucc, n + 1, targetN )
    }

  }

}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// Refl, Trans, CongSuc, ABase, ASuc, :- sum( n ) = s^n(0)
//
// where n is an Integer parameter >= 0.
object SumOfOnesExampleProof extends ProofSequence {
  val s = "s"
  val zero = "0"
  val p = "+"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  // axioms
  val Refl = All( x, Eq( x, x ) )
  val Trans = All( x, All( y, All( z, Imp( Eq( x, y ), Imp( Eq( y, z ), Eq( x, z ) ) ) ) ) )
  val CongSuc = All( x, All( y, Imp(
    Eq( x, y ),
    Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) )
  ) ) )
  val ABase = All( x, Eq( FOLFunction( p, x :: FOLConst( zero ) :: Nil ), x ) )
  val ASuc = All( x, All( y, Eq( FOLFunction( p, x :: FOLFunction( s, y :: Nil ) :: Nil ), FOLFunction( s, FOLFunction( p, x :: y :: Nil ) :: Nil ) ) ) )

  def apply( n: Int ) = proof( n )

  // TODO should be private - but scala shell does not allow access modifiers when :loading a file
  def proof( k: Int ): LKProof = {
    if ( k == 0 ) {
      val zero_eq_zero = Eq( Utils.numeral( 0 ), Utils.numeral( 0 ) )
      val p1 = ForallLeftRule( LogicalAxiom( zero_eq_zero ), Refl, Utils.numeral( 0 ) )
      val p2 = WeakeningLeftRule( p1, Trans )
      val p3 = WeakeningLeftRule( p2, CongSuc )
      val p4 = WeakeningLeftRule( p3, ABase )
      WeakeningLeftRule( p4, ASuc )
    } else if ( k == 1 ) {
      val one_eq_one = Eq( Utils.numeral( 1 ), Utils.numeral( 1 ) )
      val p1 = ForallLeftRule( LogicalAxiom( one_eq_one ), Refl, Utils.numeral( 1 ) )
      val p2 = WeakeningLeftRule( p1, Trans )
      val p3 = WeakeningLeftRule( p2, CongSuc )
      val p4 = WeakeningLeftRule( p3, ABase )
      WeakeningLeftRule( p4, ASuc )
    } else {
      /// atoms
      val ssumkm1_eq_k = Eq( FOLFunction( s, sum( k - 1 ) :: Nil ), Utils.numeral( k ) )
      val ssumkm1_eq_z = Eq( FOLFunction( s, sum( k - 1 ) :: Nil ), z )
      val sumk_eq_k = Eq( sum( k ), Utils.numeral( k ) )
      val sumk_eq_y = Eq( sum( k ), y )
      val sumk_eq_z = Eq( sum( k ), z )
      val y_eq_z = Eq( y, z )
      val sumk_eq_ssumkm1 = Eq( sum( k ), FOLFunction( s, sum( k - 1 ) :: Nil ) )
      val sumkm1_eq_km1 = Eq( sum( k - 1 ), Utils.numeral( k - 1 ) )
      val sumkm1_eq_y = Eq( sum( k - 1 ), y )
      val ssumkm1_eq_sy = Eq( FOLFunction( s, sum( k - 1 ) :: Nil ), FOLFunction( s, y :: Nil ) )

      /// prop. formulas
      val Trans2 = Imp( ssumkm1_eq_k, sumk_eq_k )
      val Trans3 = Imp( sumk_eq_ssumkm1, Trans2 )
      val CongSuc2 = Imp( sumkm1_eq_km1, ssumkm1_eq_k )

      /// quant. formulas
      val Trans3_1 = All( z, Imp( sumk_eq_ssumkm1, Imp( ssumkm1_eq_z, sumk_eq_z ) ) )
      val Trans3_2 = All( y, All( z, Imp( sumk_eq_y, Imp( y_eq_z, sumk_eq_z ) ) ) )
      val CongSuc2_1 = All( y, Imp( sumkm1_eq_y, ssumkm1_eq_sy ) )

      /// proof
      // transitivity (using aux_proof)
      val p1 = LogicalAxiom( ssumkm1_eq_k )
      val p2 = LogicalAxiom( sumk_eq_k )
      val p3 = ImpLeftRule( p1, ssumkm1_eq_k, p2, sumk_eq_k )
      val p4 = aux_proof( k - 1 )
      val p5 = ImpLeftRule( p4, sumk_eq_ssumkm1, p3, Trans2 )
      val p6 = ForallLeftRule( p5, Trans3_1, Utils.numeral( k ) )
      val p7 = ForallLeftRule( p6, Trans3_2, FOLFunction( s, sum( k - 1 ) :: Nil ) )
      val p8 = ForallLeftRule( p7, Trans, sum( k ) )
      val p9 = ContractionLeftRule( p8, Trans )

      // congruence sucessor (using IH)
      val p10 = proof( k - 1 )
      val p11 = ImpLeftRule( p10, sumkm1_eq_km1, p9, ssumkm1_eq_k )
      val p12 = ContractionLeftRule( p11, Trans )
      val p13 = ContractionLeftRule( p12, CongSuc )
      val p14 = ContractionLeftRule( p13, ASuc )
      val p15 = ContractionLeftRule( p14, ABase )
      val p16 = ForallLeftRule( p15, CongSuc2_1, Utils.numeral( k - 1 ) )
      val p17 = ForallLeftRule( p16, CongSuc, sum( k - 1 ) )
      ContractionLeftRule( p17, CongSuc )
    }
  }

  // constructs proof of: Trans, CongSuc, ASuc, ABase :- sum( k + 1 ) = s( sum( k ) )
  // TODO should be private - but scala shell does not allow access modifiers when :loading a file
  def aux_proof( k: Int ): LKProof = {
    /// atoms
    val ssumkp0_eq_ssumk = Eq( FOLFunction( s, FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ) :: Nil ), FOLFunction( s, sum( k ) :: Nil ) )
    val sumkp1_eq_ssumk = Eq( sum( k + 1 ), FOLFunction( s, sum( k ) :: Nil ) )
    val sumkp1_eq_ssumkp0 = Eq( sum( k + 1 ), FOLFunction( s, FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ) :: Nil ) )
    val ssumkp0_eq_z = Eq( FOLFunction( s, FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ) :: Nil ), z )
    val sumkp1_eq_z = Eq( sum( k + 1 ), z )
    val sumkp1_eq_y = Eq( sum( k + 1 ), y )
    val y_eq_z = Eq( y, z )
    val sumkp0_eq_sumk = Eq( FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ), sum( k ) )
    val sumkp0_eq_y = Eq( FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ), y )
    val ssumkp0_eq_sy = Eq( FOLFunction( s, FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ) :: Nil ), FOLFunction( s, y :: Nil ) )
    val sumkpsy_eq_ssumkpy = Eq( FOLFunction( p, sum( k ) :: FOLFunction( s, y :: Nil ) :: Nil ), FOLFunction( s, FOLFunction( p, sum( k ) :: y :: Nil ) :: Nil ) )

    /// prop. formulas
    val Trans2 = Imp( ssumkp0_eq_ssumk, sumkp1_eq_ssumk )
    val Trans3 = Imp( sumkp1_eq_ssumkp0, Trans2 )
    val Cong2 = Imp( sumkp0_eq_sumk, ssumkp0_eq_ssumk )

    /// quant. formulas
    val Trans3_1 = All( z, Imp( sumkp1_eq_ssumkp0, Imp( ssumkp0_eq_z, sumkp1_eq_z ) ) )
    val Trans3_2 = All( y, All( z, Imp( sumkp1_eq_y, Imp( y_eq_z, sumkp1_eq_z ) ) ) )
    val Cong2_1 = All( y, Imp( sumkp0_eq_y, ssumkp0_eq_sy ) )
    val ASuc_1 = All( y, sumkpsy_eq_ssumkpy )

    /// proof
    // transitivity
    val p1 = LogicalAxiom( ssumkp0_eq_ssumk )
    val p2 = LogicalAxiom( sumkp1_eq_ssumk )
    val p3 = ImpLeftRule( p1, ssumkp0_eq_ssumk, p2, sumkp1_eq_ssumk )
    val p4 = LogicalAxiom( sumkp1_eq_ssumkp0 )
    val p5 = ImpLeftRule( p4, sumkp1_eq_ssumkp0, p3, Trans2 )
    val p6 = ForallLeftRule( p5, Trans3_1, FOLFunction( s, sum( k ) :: Nil ) )
    val p7 = ForallLeftRule( p6, Trans3_2, FOLFunction( s, FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ) :: Nil ) )
    val p8 = ForallLeftRule( p7, Trans, sum( k + 1 ) )

    // congruence sucessor
    val p9 = LogicalAxiom( sumkp0_eq_sumk )
    val p10 = ImpLeftRule( p9, sumkp0_eq_sumk, p8, ssumkp0_eq_ssumk )
    val p11 = ForallLeftRule( p10, Cong2_1, sum( k ) )
    val p12 = ForallLeftRule( p11, CongSuc, FOLFunction( p, sum( k ) :: Utils.numeral( 0 ) :: Nil ) )

    // addition sucessor case
    val p13 = ForallLeftRule( p12, ASuc_1, Utils.numeral( 0 ) )
    val p14 = ForallLeftRule( p13, ASuc, sum( k ) )

    // addition base case
    ForallLeftRule( p14, ABase, sum( k ) )
  }

  // the term (.((1 + 1) + 1 ) + ... + 1 ), k must be at least 1
  // TODO should be private - but scala shell does not allow access modifiers when :loading a file
  def sum( k: Int ): FOLTerm = {
    if ( k == 1 ) Utils.numeral( 1 )
    else FOLFunction( p, sum( k - 1 ) :: Utils.numeral( 1 ) :: Nil )
  }
}

/**
 * Auxiliary structure to deal with axioms of the schema:
 * Forall variables cond1 -> cond2 -> ... -> condn -> consequence |- ...
 */
class AllQuantifiedConditionalAxiomHelper( variables: List[FOLVar], conditions: List[FOLAtom], consequence: FOLFormula ) {
  /**
   * Returns the full axiom
   */
  def getAxiom: FOLFormula = {
    // TODO: refactor apply_conditional_equality, combine duplicate code
    val impl_chain = ( conditions :\ consequence )( ( c, acc ) => Imp( c, acc ) )

    All.Block( variables, impl_chain )
  }

  /**
   * Use axiom with given expressions in proof.
   * Consequence of axiom must appear in current proof.
   * Instantiated conditions will of course remain in the antecedent of the returned proof
   */
  def apply( expressions: List[FOLTerm], p: LKProof ): LKProof = {
    assert( expressions.length == variables.length, "Number of expressions doesn't equal number of variables" )

    // construct implication with instantiated conditions and consequence
    val ( instantiated_conditions, instantiated_consequence ) = ( ( conditions -> consequence ) /: variables.indices ) { ( acc, i ) =>
      val substitute = ( x: FOLFormula ) => FOLSubstitution( variables( i ), expressions( i ) )( x )
      ( acc._1.map( substitute ).asInstanceOf[List[FOLAtom]], substitute( acc._2 ) )
    }

    val p1 = apply_conditional_equality( instantiated_conditions, instantiated_consequence, p )

    // iteratively instantiate all-quantified variables with expression
    def instantiate_axiom( expressions: List[FOLTerm], axiom: FOLFormula, p: LKProof ): LKProof = {
      expressions match {
        case Nil => p
        case head :: tail =>
          val new_axiom = instantiate( axiom, head )
          val new_p = instantiate_axiom( tail, new_axiom, p )

          ForallLeftRule( new_p, axiom, head )

      }
    }

    val ax = getAxiom
    val p2 = instantiate_axiom( expressions, ax, p1 )

    ContractionLeftRule( p2, ax )
  }

  private def apply_conditional_equality( equalities: List[FOLAtom], result: FOLFormula, p: LKProof ): LKProof = {
    equalities match {
      case Nil =>
        p // no conditions at all

      case head :: Nil =>
        val ax = LogicalAxiom( head )
        ImpLeftRule( ax, head, p, result )

      case head :: tail =>
        val ax = LogicalAxiom( head )
        val impl_chain = ( tail :\ result )( ( c, acc ) => Imp( c, acc ) )

        val s2 = apply_conditional_equality( tail, result, p )
        ImpLeftRule( ax, head, s2, impl_chain )

    }
  }
}

object UniformAssociativity3ExampleProof extends ProofSequence {

  val s = "s"
  val p = "+"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  val x1 = FOLVar( "x_1" )
  val x2 = FOLVar( "x_2" )
  val y1 = FOLVar( "y_1" )
  val y2 = FOLVar( "y_2" )

  def f1( sym: String, arg: FOLTerm ) = FOLFunction( sym, arg :: Nil )
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ): FOLTerm = FOLFunction( sym, arg1 :: arg2 :: Nil )
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ): FOLTerm = f2( sym, arg1, arg2 )

  // Axioms

  // Trans as from TransRule, possibly unify or generalise
  val Trans = All( x, All( y, All( z, Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) ) ) ) )
  val Symm = All( x, Eq( x, x ) )
  val Cs = All( x, All( y, Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) ) ) )

  // TODO: port these axioms to new format using AllQuantifiedConditionalAxiomHelper
  def refl_ax(): FOLFormula = All( x, refl_ax( x ) )
  def refl_ax( x: FOLTerm ): FOLFormula = All( y, refl_ax( x, y ) )
  def refl_ax( x: FOLTerm, y: FOLTerm ): FOLFormula = Imp( Eq( x, y ), Eq( y, x ) )

  // x=y -> s(x) = s(y)
  def cs_ax(): FOLFormula = All( x, cs_ax( x ) )
  def cs_ax( x: FOLTerm ): FOLFormula = All( y, cs_ax( x, y ) )
  def cs_ax( x: FOLTerm, y: FOLTerm ): FOLFormula = Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) )

  // x1 = x2 -> y1 = y2 -> x1 + y1 = x2 + y2
  val cp = new AllQuantifiedConditionalAxiomHelper( x1 :: x2 :: y1 :: y2 :: Nil, Eq( x1, x2 ) :: Eq( y1, y2 ) :: Nil, Eq( FOLFunction( p, x1 :: y1 :: Nil ), FOLFunction( p, x2 :: y2 :: Nil ) ) )

  // Arithmetic axioms
  val Ax1 = All( x, Eq( FOLFunction( p, x :: Utils.numeral( 0 ) :: Nil ), x ) )

  // Forall x, y: s(x+y) = x+s(y)
  def ax2_ax(): FOLFormula = All( x, All( y, ax2_ax( x, y ) ) )
  def ax2_ax( x: FOLTerm ): FOLFormula = All( y, ax2_ax( x, y ) )
  def ax2_ax( x: FOLTerm, y: FOLTerm ): FOLFormula = Eq( f1( s, f2( x, p, y ) ), f2( x, p, f1( s, y ) ) )

  def addAllAxioms( proof: LKProof ): LKProof =
    Seq( Trans, cp.getAxiom, Symm, ax2_ax(), cs_ax(), refl_ax(), Ax1 ).foldLeft( proof )( WeakeningLeftRule( _, _ ) )

  def apply( n: Int ): LKProof = {
    assert( n >= 0, "n must be >= 0" )
    val proof = if ( n > 0 ) {
      gen_proof_step( 0, n )
    } else {
      val zero = Utils.numeral( 0 )
      val c1 = f2( f2( zero, p, zero ), p, zero )
      val e1 = f2( zero, p, f2( zero, p, zero ) )
      addAllAxioms( LogicalAxiom( Eq( c1, e1 ) ) )
    }
    induction_start( n, proof )
  }

  /**
   * Close off proof ending in (n + n) + 0 = n + (n + 0) |- ...
   */
  def induction_start( n: Int, p0: LKProof ): LKProof = {
    // show both sides equal to n + n
    val n_num = Utils.numeral( n )
    val zero = Utils.numeral( 0 )
    val c1 = f2( f2( n_num, p, n_num ), p, zero )
    val d1 = f2( n_num, p, n_num )
    val e1 = f2( n_num, p, f2( n_num, p, zero ) )
    val p1 = TransRule( c1, d1, e1, p0 )

    // show (n + n) + 0 = (n + n) directly via ax1
    val p2 = ForallLeftRule( p1, Ax1, d1 )
    val p3 = ContractionLeftRule( p2, Ax1 )

    // show (n + n) = n + (n + 0) 
    val p4 = cp( n_num :: n_num :: n_num :: f2( n_num, p, zero ) :: Nil, p3 )

    // show n = n and n = n + 0
    val p5 = ForallLeftRule( p4, Symm, n_num )
    val p6 = ContractionLeftRule( p5, Symm )

    val p7 = reflect( f2( n_num, p, zero ), n_num, p6 )

    val p8 = ForallLeftRule( p7, Ax1, n_num )
    ContractionLeftRule( p8, Ax1 )
  }

  /**
   * *
   * Returns proof Pi (currently including line above and below Pi), with numerals n, i, i+1:
   * (n + n) + i+1 = n + (n + i+1), Ax |- ...
   *  Pi
   * (n + n) + i   = n + (n + i), Ax |- ...
   */
  def gen_proof_step( i: Int, n: Int ): LKProof = {
    val n_num = Utils.numeral( n )
    val i_num = Utils.numeral( i )
    val ip1_num = Utils.numeral( i + 1 )

    val a1 = f2( f2( n_num, p, n_num ), p, ip1_num )
    val a2 = f2( n_num, p, f2( n_num, p, ip1_num ) )
    val b1 = f2( n_num, p, f1( s, f2( p, n_num, i_num ) ) )

    val p0 =
      if ( i + 1 >= n ) {
        val final_expression = Eq( a1, a2 )

        val top = Axiom( final_expression :: Nil, final_expression :: Nil )
        addAllAxioms( top )
      } else {
        gen_proof_step( i + 1, n )
      }

    val p1 = TransRule( a1, b1, a2, p0 )

    // the left side now contains
    // (n + n) + s(i) = n + s(n + i) as well as
    // n + s(n + i) = n + (n + s(i))

    // use Cp to reduce the latter to s(n + i) = (n + s(i))
    val x1_1 = n_num
    val x2_1 = n_num
    val y1_1 = f1( s, f2( n_num, p, i_num ) )
    val y2_1 = f2( n_num, p, f1( s, i_num ) )
    val p8 = cp( x1_1 :: x2_1 :: y1_1 :: y2_1 :: Nil, p1 )

    // show x1 = x2 by symmetry
    val p9 = ForallLeftRule( p8, Symm, n_num )
    val p10 = ContractionLeftRule( p9, Symm )

    // show y1 = y2 by Ax2 (i.e. s(n + i) = (n + s(i)) )
    val p13 = show_by_ax2( n_num, i_num, p10 )

    // now we only have (n + n) + s(i) = n + s(n + i) left (c=e), reduce right hand side by Ax2 and Trans to s(n + (n + i) (c=d) )
    val c1 = f2( f2( n_num, p, n_num ), p, f1( s, i_num ) )
    val d1 = f1( s, f2( n_num, p, f2( n_num, p, i_num ) ) )
    val e1 = f2( n_num, p, f1( s, f2( n_num, p, i_num ) ) )
    val p14 = TransRule( c1, d1, e1, p13 )

    // show d=e by Ax2
    val p15 = show_by_ax2( n_num, f2( n_num, p, i_num ), p14 )

    // next goal: reduce (n + n) + s(i) = s(n + (n + i) to (n + n) + s(i) = s( (n + n) + i) using the IH, Trans and Cs)
    val c2 = f2( f2( n_num, p, n_num ), p, f1( s, i_num ) )
    val d2 = f1( s, f2( f2( n_num, p, n_num ), p, i_num ) )
    val e2 = d1
    val p16 = TransRule( c2, d2, e2, p15 )

    val p17 = show_by_cs( f2( f2( n_num, p, n_num ), p, i_num ), f2( n_num, p, f2( n_num, p, i_num ) ), p16 )

    // now we have:
    // (n + n) + s(i) = s( (n + n) + i) 
    // as well as
    // (n + n) + i = n + (n + i)
    // -> use Ax2

    // use reflection to match definition of ax2 afterwards
    val p18 = reflect( d2, c2, p17 )

    val p19 = show_by_ax2( f2( n_num, p, n_num ), i_num, p18 )
    p19

    // we end up with the IH (n + n) + i = n + (n + i)
  }

  def show_by_ax2( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = ForallLeftRule( p, ax2_ax( x ), y )
    val p2 = ForallLeftRule( p1, ax2_ax(), x )
    ContractionLeftRule( p2, ax2_ax() )
  }

  def show_by_cs( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = apply_conditional_equality( Eq( x, y ) :: Nil, Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ), p )

    val p2 = ForallLeftRule( p1, cs_ax( x ), y )
    val p3 = ForallLeftRule( p2, cs_ax(), x )
    ContractionLeftRule( p3, cs_ax() )
  }

  /**
   * Takes a proof s2 with end-sequent of the form
   * (x=y), ... |- ...
   * and return one with end-sequent of the form
   * (y=x), ... |- ...
   */
  def reflect( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = apply_conditional_equality( Eq( x, y ) :: Nil, Eq( y, x ), p )

    val p2 = ForallLeftRule( p1, refl_ax( x ), y )
    val p3 = ForallLeftRule( p2, refl_ax(), x )
    ContractionLeftRule( p3, refl_ax() )
  }

  def apply_conditional_equality( equalities: List[FOLFormula], result: FOLFormula, p: LKProof ): LKProof = {
    equalities match {
      case Nil => p
      case head :: Nil => {
        val ax = Axiom( head :: Nil, head :: Nil )
        ImpLeftRule( ax, head, p, result )
      }
      case head :: tail => {
        val ax = Axiom( head :: Nil, head :: Nil )
        var impl_chain = result
        for ( elem <- tail.reverse ) {
          impl_chain = Imp( elem, impl_chain )
        }
        val s2 = apply_conditional_equality( tail, result, p )
        ImpLeftRule( ax, head, s2, impl_chain )
      }
    }
  }
}

/**
 * Proof of f(n) = g(n, 1), where f is the head recursive and g the tail recursive formulation of the factorial function
 */
object FactorialFunctionEqualityExampleProof extends ProofSequence {

  val p = "+"
  val m = "*"
  val s = "s"
  val f = "f"
  val g = "g"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  def f1( sym: String, arg: FOLTerm ) = FOLFunction( sym, arg :: Nil )
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ): FOLTerm = FOLFunction( sym, arg1 :: arg2 :: Nil )
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ): FOLTerm = f2( sym, arg1, arg2 )

  val f_ax_1 = Eq( f1( f, Utils.numeral( 0 ) ), f1( s, Utils.numeral( 0 ) ) )
  val f_ax_2 = Prover9TermParserLadrStyle.parseFormula( "(all x f(s(x)) = s(x) * f(x))" )

  val g_ax_1 = new AllQuantifiedConditionalAxiomHelper( y :: Nil, Nil, Eq( y, f2( g, Utils.numeral( 0 ), y ) ) )
  val g_ax_2 = Prover9TermParserLadrStyle.parseFormula( "(all x (all y g(s(x), y) = g(x, y * s(x))))" )

  val g_compat_2 = new AllQuantifiedConditionalAxiomHelper( x :: y :: z :: Nil, Eq( y, z ) :: Nil, Eq( f2( g, x, y ), f2( g, x, z ) ) )

  val trans_axiom = new AllQuantifiedConditionalAxiomHelper( x :: y :: z :: Nil, Eq( x, y ) :: Eq( y, z ) :: Nil, Eq( x, z ) )
  val symm_axiom = All( x, Eq( x, x ) )
  val refl_axiom = new AllQuantifiedConditionalAxiomHelper( x :: y :: Nil, Eq( x, y ) :: Nil, Eq( y, x ) )
  val compat_mul_axiom = new AllQuantifiedConditionalAxiomHelper( x :: y :: z :: Nil, Eq( x, y ) :: Nil, Eq( f2( z, m, x ), f2( z, m, y ) ) )
  val assoc_mul_axiom = new AllQuantifiedConditionalAxiomHelper( x :: y :: z :: Nil, Nil, Eq( f2( x, m, f2( y, m, z ) ), f2( f2( x, m, y ), m, z ) ) )

  val mul_neutral_axiom = new AllQuantifiedConditionalAxiomHelper( x :: Nil, Nil, Eq( f2( x, m, Utils.numeral( 1 ) ), x ) )
  // this second axiom saves us from adding commutativity of multiplication
  val mul_neutral_axiom_2 = new AllQuantifiedConditionalAxiomHelper( x :: Nil, Nil, Eq( f2( Utils.numeral( 1 ), m, x ), x ) )

  def apply( n: Int ): LKProof = n match {
    case 0 =>
      val targetEquation = Eq( f1( f, Utils.numeral( 0 ) ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) )
      val g0 = Eq( Utils.numeral( 1 ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) )
      val ax1 = LogicalAxiom( f_ax_1 )
      val ax2 = LogicalAxiom( g0 )
      val ax3 = LogicalAxiom( targetEquation )
      val p1 = ImpLeftRule( ax2, g0, ax3, targetEquation )
      val p2 = ImpLeftRule( ax1, f_ax_1, p1, Imp( g0, targetEquation ) )
      val p3 = ForallLeftBlock( p2, trans_axiom.getAxiom, Seq( f1( f, Utils.numeral( 0 ) ), Utils.numeral( 1 ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) ) )
      val p4 = ForallLeftRule( p3, g_ax_1.getAxiom, Utils.numeral( 1 ) )
      WeakeningLeftMacroRule(
        p4,
        List( f_ax_2, g_ax_2, symm_axiom, refl_axiom.getAxiom,
          compat_mul_axiom.getAxiom, assoc_mul_axiom.getAxiom, g_compat_2.getAxiom,
          mul_neutral_axiom.getAxiom, mul_neutral_axiom_2.getAxiom )
      )
    case _ => induction_steps( n )
  }

  def induction_steps( n: Int ): LKProof = {
    val axiom_formulae = Eq( f1( f, Utils.numeral( n ) ), f2( g, Utils.numeral( n ), Utils.numeral( 1 ) ) ) :: Nil
    val axiom: LKProof = Axiom( axiom_formulae, axiom_formulae )

    // add axioms
    val all_axioms = List[FOLFormula]( f_ax_1, f_ax_2, g_ax_1.getAxiom, g_ax_2, symm_axiom, refl_axiom.getAxiom,
      trans_axiom.getAxiom, compat_mul_axiom.getAxiom, assoc_mul_axiom.getAxiom, g_compat_2.getAxiom,
      mul_neutral_axiom.getAxiom, mul_neutral_axiom_2.getAxiom )
    val p1 = all_axioms.foldLeft( axiom )( ( proof, elem ) => WeakeningLeftRule( proof, elem ) )

    val n_num = Utils.numeral( n )

    /**
     * Returns (( ([start_value*]n)*(n-1) ) * ... * ) k
     */
    def get_partial_factorial_term( n: Int, k: Int, start_value: Option[FOLTerm] = None ): FOLTerm = {
      if ( n <= k ) {
        if ( n == k ) {
          start_value match {
            case Some( value ) => f2( value, m, Utils.numeral( n ) )
            case None          => Utils.numeral( n )
          }
        } else throw new Exception( "k larger than n in partial factorial" )
      } else {
        f2( m, get_partial_factorial_term( n, k + 1, start_value ), Utils.numeral( k ) )
      }
    }

    def induction_step_rec( p0: LKProof, k: Int ): LKProof = {

      val k_num = Utils.numeral( k )
      val zero = Utils.numeral( 0 )
      val one = Utils.numeral( 1 )

      val part_fac = if ( n == k ) one else get_partial_factorial_term( n, k + 1 )
      val part_fac_next = get_partial_factorial_term( n, k )

      val f_k_term = if ( n == k ) f1( f, k_num ) // f(k)
      else f2( m, part_fac, f1( f, k_num ) ) // part_fac * f(k)

      val g_k_term = f2( g, k_num, part_fac )

      if ( k == 0 ) {
        // we have: n! * f(0) = g(0, ( ... (( (1 * n) * (n-1) ) * (n-2) ) * ... ) * 1 )

        // use f(0) = s(0)
        val p1 = trans_axiom( List( f_k_term, f2( part_fac, m, f1( s, zero ) ), g_k_term ), p0 )
        val p2 = compat_mul_axiom( List( f1( f, zero ), f1( s, zero ), part_fac ), p1 )
        val p3 = ContractionLeftRule( p2, f_ax_1 )

        // use g(0, y) = y
        val p4 = trans_axiom( List( f2( part_fac, m, f1( s, zero ) ), part_fac, g_k_term ), p3 )
        val p5 = g_ax_1( part_fac :: Nil, p4 )

        // the formula actually says n! * 1 = n!, we have to get rid of the 1
        val p6 = trans_axiom( List( f2( part_fac, m, one ), part_fac, part_fac ), p5 )
        val p7 = mul_neutral_axiom( List( part_fac ), p6 )
        val p8 = ForallLeftRule( p7, symm_axiom, part_fac )
        val p9 = ContractionLeftRule( p8, symm_axiom )

        p9
      } else {
        // lhs contains part_fac * f(k) = g(k, part_fac)

        val km1_num = Utils.numeral( k - 1 ) // must not be evaluated for k == 0
        val f_km1_term = f2( m, part_fac_next, f1( f, km1_num ) ) // (part_fac * k) * f(k-1)
        val g_km1_term = f2( g, km1_num, part_fac_next )

        // first step: decompose f: part_fac * k * f(k-1) = g(k, 1*part_fac)
        val p1 = trans_axiom( List( f_k_term, f_km1_term, g_k_term ), p0 )

        val p3 =
          if ( n == k ) {
            // use axiom directly, part_fac is empty
            val p1_0 = ForallLeftRule( p1, f_ax_2, km1_num )
            ContractionLeftRule( p1_0, f_ax_2 )
          } else {
            // the antecedent contains something along the lines of:
            // 4*f(3) = (4*3) * f(2) or
            // (4*3)*f(2) = ((4*3)*2) * f(1)
            // we however need the last part exposed and grouped to be able to use compat & f_ax2 to show it, like in: 4*f(3) = 4* (3*f(2))
            // use Trans to expose it and show it, other part can be shown by associativity
            // step in between (=yTrans):
            // 4 * (3*f(2)) or
            // (4*3) * (2*f(1))
            val yTrans = f2( part_fac, m, f2( k_num, m, f1( f, km1_num ) ) )
            val p1_0 = trans_axiom( f_k_term :: yTrans :: f_km1_term :: Nil, p1 )
            // show by compat, then f_ax_2: part_fac * f(k) = part_fac * (k * f(k-1))
            val f_k = f1( f, k_num )
            val k_f_km1 = f2( k_num, m, f1( f, km1_num ) )
            val p1_1 = compat_mul_axiom( List( f_k, k_f_km1, part_fac ), p1_0 )
            val p1_2 = ForallLeftRule( p1_1, f_ax_2, km1_num )
            val p1_3 = ContractionLeftRule( p1_2, f_ax_2 )
            // show by assoc: part_fac * (k * f(k-1)) = (part_fac * k) * f(k-1)
            val p1_4 = assoc_mul_axiom( List( part_fac, k_num, f1( f, km1_num ) ), p1_3 )
            p1_4
          }

        // now transform k * f(k-1) = g(k, part_fac) to k * f(k-1) = g(k-1, part_fac * k)
        val p4 = trans_axiom( List( f_km1_term, g_km1_term, g_k_term ), p3 )

        // show g(k, part_fac) = g(k-1, part_fac*k) (need to use reflection to get to this form first)
        val p4_2 = refl_axiom( g_k_term :: g_km1_term :: Nil, p4 )

        val p5 =
          if ( n == k ) {
            // g is initially called with a 1 as second argument, but we want to get rid of it to make the final result equal to the one f produces
            // use trans to split into g-axiom part and part where the two expressions only differ by this extra one
            val g_intermed = f2( g, km1_num, f2( one, m, part_fac_next ) )
            val p5_1 = trans_axiom( g_k_term :: g_intermed :: g_km1_term :: Nil, p4_2 )
            // show g(n, 1) = g(n-1, 1*n) by g_ax_2
            val intermed = All( y, Eq( f2( g, k_num, y ), f2( g, km1_num, f2( y, m, k_num ) ) ) )
            val p5_2 = ForallLeftRule( p5_1, intermed, one )
            val p5_3 = ForallLeftRule( p5_2, g_ax_2, km1_num )
            val p5_4 = ContractionLeftRule( p5_3, g_ax_2 )

            // show g(n-1, 1*n) = g(n-1, n) by g_compat_2
            val p5_5 = g_compat_2( List( km1_num, f2( one, m, k_num ), k_num ), p5_4 )
            // show 1 * k = k
            val p5_6 = mul_neutral_axiom_2( List( k_num ), p5_5 )
            p5_6
          } else {
            val intermed = All( y, Eq( f2( g, f1( s, km1_num ), y ), f2( g, km1_num, f2( m, y, f1( s, km1_num ) ) ) ) )
            val p6 = ForallLeftRule( p4_2, intermed, part_fac )
            val p7 = ForallLeftRule( p6, g_ax_2, km1_num )
            val p8 = ContractionLeftRule( p7, g_ax_2 )
            p8
          }

        induction_step_rec( p5, k - 1 )
      }
    }

    induction_step_rec( p1, n )
  }
}

object FactorialFunctionEqualityExampleProof2 extends ProofSequence {
  import at.logic.gapt.expr.fol.Utils.{ numeral => num }

  val zero = FOLConst( "0" )
  val one = s( zero )
  val alpha = FOLVar( "α" )
  val beta = FOLVar( "β" )
  val nu = FOLVar( "ν" )
  val gamma = FOLVar( "γ" )

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )
  val w = FOLVar( "w" )

  def s( x: FOLTerm ) = FOLFunction( "s", List( x ) )
  def m( x: FOLTerm, y: FOLTerm ) = FOLFunction( "*", x, y )
  def f( x: FOLTerm ) = FOLFunction( "f", List( x ) )
  def g( x: FOLTerm, y: FOLTerm ) = FOLFunction( "g", x, y )

  def f0 = Eq( f( zero ), s( zero ) )
  def fST( x: FOLTerm ) = Eq( f( s( x ) ), m( s( x ), f( x ) ) )
  def g0( x: FOLTerm ) = Eq( g( x, zero ), x )
  def gST( x: FOLTerm, y: FOLTerm ) = Eq( g( x, s( y ) ), g( m( x, s( y ) ), y ) )
  def uR( x: FOLTerm ) = Eq( m( x, s( zero ) ), x )
  def uL( x: FOLTerm ) = Eq( m( s( zero ), x ), x )
  def ASSO( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Eq( m( m( x, y ), z ), m( x, m( y, z ) ) )
  def target( x: FOLTerm ) = Eq( f( x ), g( s( zero ), x ) )

  def apply( n: Int ): LKProof = {
    /**
     * Computes 1 * n * (n- 1) * … * k, associated to the left.
     *
     */
    def product( k: Int ) =
      ( one /: ( k until n + 1 ).reverse ) { ( acc: FOLTerm, i: Int ) =>
        m( acc, num( i ) )
      }

    /*val axiom = ReflexivityAxiom( product( 1 ) )

    val p1 = ParamodulationRightRule( LogicalAxiom( uR( product( 1 ) ) ), uR( product( 1 ) ), axiom, Eq( product( 1 ), product( 1 ) ), Eq( m( product( 1 ), one ), product( 1 ) ) )
    val p2 = ParamodulationRightRule( LogicalAxiom( f0 ), f0, p1, Eq( m( product( 1 ), one ), product( 1 ) ), Eq( m( product( 1 ), f( zero ) ), product( 1 ) ) )
    val p3 = ParamodulationRightRule( LogicalAxiom( g0( product( 1 ) ) ), g0( product( 1 ) ), p2, Eq( m( product( 1 ), f( zero ) ), product( 1 ) ), Eq( m( product( 1 ), f( zero ) ), g( product( 1 ), zero ) ) )
    val p4 = ForallLeftRule( p3, All( x, uR( x ) ), product( 1 ) )
    val p5 = ForallLeftRule( p4, All( x, g0( x ) ), product( 1 ) )

    val p6 = ( 0 until n ).foldLeft[LKProof]( p5 ) { ( acc: LKProof, i: Int ) =>
      val tmp1 = ParamodulationRightRule( LogicalAxiom( ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ) ), ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ), acc, Eq( m( product( i + 1 ), f( num( i ) ) ), g( product( i + 1 ), num( i ) ) ), Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ) )
      val tmp2 = ForallLeftBlock( tmp1, univclosure( ASSO( x, y, z ) ), List( product( i + 2 ), num( i + 1 ), f( num( i ) ) ) )
      val tmp3 = ParamodulationRightRule( LogicalAxiom( fST( num( i ) ) ), fST( num( i ) ), tmp2, Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ), Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ) )
      val tmp4 = ParamodulationRightRule( LogicalAxiom( gST( product( i + 2 ), num( i ) ) ), gST( product( i + 2 ), num( i ) ), tmp3, Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ), Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 2 ), num( i + 1 ) ) ) )
      val tmp5 = ForallLeftRule( tmp4, univclosure( fST( x ) ), num( i ) )
      val tmp6 = ForallLeftBlock( tmp5, univclosure( gST( x, y ) ), List( product( i + 2 ), num( i ) ) )
      ContractionMacroRule( tmp6 )
    }

    val p7 = ParamodulationRightRule( LogicalAxiom( uL( f( num( n ) ) ) ), uL( f( num( n ) ) ), p6, Eq( m( one, f( num( n ) ) ), g( one, num( n ) ) ), target( num( n ) ) )
    WeakeningContractionMacroRule( ForallLeftRule( p7, All( x, uL( x ) ), f( num( n ) ) ), endSequent( n ) )
*/
    val p1 = ( ProofBuilder
      c ReflexivityAxiom( product( 1 ) )
      u ( WeakeningLeftMacroRule( _, Seq( uR( product( 1 ) ), f0, g0( product( 1 ) ) ) ) )
      u ( EqualityRightRule( _, uR( product( 1 ) ), Eq( product( 1 ), product( 1 ) ), Eq( m( product( 1 ), one ), product( 1 ) ) ) )
      u ( EqualityRightRule( _, f0, Eq( m( product( 1 ), one ), product( 1 ) ), Eq( m( product( 1 ), f( zero ) ), product( 1 ) ) ) )
      u ( EqualityRightRule( _, g0( product( 1 ) ), Eq( m( product( 1 ), f( zero ) ), product( 1 ) ), Eq( m( product( 1 ), f( zero ) ), g( product( 1 ), zero ) ) ) )
      u ( ForallLeftRule( _, All( x, uR( x ) ), product( 1 ) ) )
      u ( ForallLeftRule( _, All( x, g0( x ) ), product( 1 ) ) ) qed )

    val p2 = ( 0 until n ).foldLeft[LKProof]( p1 ) { ( acc: LKProof, i: Int ) =>
      ( ProofBuilder
        c acc
        u ( WeakeningLeftMacroRule( _, Seq( ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ), fST( num( i ) ), gST( product( i + 2 ), num( i ) ) ) ) )
        u ( EqualityRightRule( _, ASSO( product( i + 2 ), num( i + 1 ), f( num( i ) ) ), Eq( m( product( i + 1 ), f( num( i ) ) ), g( product( i + 1 ), num( i ) ) ), Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ) ) )
        u ( ForallLeftBlock( _, univclosure( ASSO( x, y, z ) ), List( product( i + 2 ), num( i + 1 ), f( num( i ) ) ) ) )
        u ( EqualityRightRule( _, fST( num( i ) ), Eq( m( product( i + 2 ), m( num( i + 1 ), f( num( i ) ) ) ), g( product( i + 1 ), num( i ) ) ), Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ) ) )
        u ( EqualityRightRule( _, gST( product( i + 2 ), num( i ) ), Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 1 ), num( i ) ) ), Eq( m( product( i + 2 ), f( num( i + 1 ) ) ), g( product( i + 2 ), num( i + 1 ) ) ) ) )
        u ( ForallLeftRule( _, univclosure( fST( x ) ), num( i ) ) )
        u ( ForallLeftBlock( _, univclosure( gST( x, y ) ), List( product( i + 2 ), num( i ) ) ) )
        u ( ContractionMacroRule( _ ) ) qed )
    }

    ( ProofBuilder
      c p2
      u ( WeakeningLeftRule( _, uL( f( num( n ) ) ) ) )
      u ( EqualityRightRule( _, uL( f( num( n ) ) ), Eq( m( one, f( num( n ) ) ), g( one, num( n ) ) ), target( num( n ) ) ) )
      u ( ForallLeftRule( _, All( x, uL( x ) ), f( num( n ) ) ) )
      u ( WeakeningContractionMacroRule( _, endSequent( n ) ) ) qed )
  }

  def endSequent( n: Int ): HOLSequent = HOLSequent(
    List(
      f0,
      fST( x ),
      g0( x ),
      gST( x, y ),
      uR( x ),
      uL( x ),
      ASSO( x, y, z )
    ) map univclosure.apply,
    List(
      target( num( n ) )
    )
  )
}

