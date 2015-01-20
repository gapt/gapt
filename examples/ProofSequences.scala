/**********
 * Example proof sequences, usage example from CLI:
 *
 * scala> :load examples/ProofSequences.scala
 * scala> val p = LinearExampleProof( 5 )
 **********/

import at.logic.language.fol.Substitution

// Functions to construct cut-free FOL LK proofs of the sequents
//
// P(0), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
//
// where n is an Integer parameter >= 0.
object LinearExampleProof {
  val s = "s"
  val p = "P"
  val c = "0"

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0)), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
  def proof( k: Int, n: Int )  : LKProof =
  {
    val x = FOLVar( "x" )
    val ass = AllVar( x, Imp( Atom( p, x::Nil ), Atom( p, Function( s, x::Nil )::Nil ) ) )
    if ( k == n ) // leaf proof
    {
      val a = Atom( p,  Utils.numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val p1 = Atom( p, Utils.numeral( k )::Nil )
      val p2 = Atom( p, Utils.numeral( k + 1 )::Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1::Nil, p1::Nil ), proof( k + 1, n ), p1, p2 ), aux, ass, Utils.numeral( k ) ), ass )
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
object SquareDiagonalExampleProof {
  val s = "s"
  val p = "P"
  val c = "0"

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0),s^k(0)), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y . P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
  def proof( k: Int, n: Int )  : LKProof =
  {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )

    val assx = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, Function( s, x::Nil )::y::Nil ) ) ) )
    def assx_aux( k: Int ) = AllVar( y, Imp( Atom( p, Utils.numeral( k )::y::Nil ), Atom(p, Utils.numeral( k + 1 )::y::Nil ) ) )

    val assy = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, x::Function( s, y::Nil )::Nil ) ) ) )
    def assy_aux( k: Int ) = AllVar( y, Imp( Atom( p, Utils.numeral( k )::y::Nil ), Atom(p, Utils.numeral( k )::Function( s, y::Nil )::Nil ) ) )
 
    if ( k == n ) // leaf proof
    {
      val a = Atom( p, Utils.numeral( n )::Utils.numeral( n )::Nil )
      WeakeningLeftRule( WeakeningLeftRule( Axiom( a:: Nil, a::Nil ), assx ), assy )
    }
    else
    {
      val ayl = Atom( p, Utils.numeral( k + 1 )::Utils.numeral( k )::Nil ) // atom y left
      val ayr = Atom( p, Utils.numeral( k + 1 )::Utils.numeral( k + 1 )::Nil )
      val auxy = Imp( ayl, ayr )

      val p1 = ImpLeftRule( Axiom( ayl::Nil, ayl::Nil ), proof( k + 1, n), ayl, ayr )
      val p2 = ForallLeftRule( p1, auxy, assy_aux( k + 1 ), Utils.numeral( k ) )
      val p3 = ForallLeftRule( p2, assy_aux( k + 1 ), assy, Utils.numeral( k + 1) )
      val p4 = ContractionLeftRule( p3, assy )

      val axl = Atom( p, Utils.numeral( k )::Utils.numeral( k )::Nil ) // atom x left
      val axr = Atom( p, Utils.numeral( k + 1 )::Utils.numeral( k )::Nil )
      val auxx = Imp( axl, axr )

      val p5 = ImpLeftRule( Axiom( axl::Nil, axl::Nil ), p4, axl, axr )
      val p6 = ForallLeftRule( p5, auxx, assx_aux( k ), Utils.numeral( k ) )
      val p7 = ForallLeftRule( p6, assx_aux( k ), assx, Utils.numeral( k ) )
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
object SquareEdgesExampleProof {
  val s = "s"
  val p = "P"
  val c = "0"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  val assx = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, Function( s, x::Nil )::y::Nil ) ) ) )
  def assx_aux( k: Int ) = AllVar( y, Imp( Atom( p, Utils.numeral( k )::y::Nil ), Atom(p, Utils.numeral( k + 1 )::y::Nil ) ) )

  val assy = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, x::Function( s, y::Nil )::Nil ) ) ) )
  def assy_aux( k: Int ) = AllVar( y, Imp( Atom( p, Utils.numeral( k )::y::Nil ), Atom(p, Utils.numeral( k )::Function( s, y::Nil )::Nil ) ) )
 
  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^k(0),0), \ALL x \ALL y. P(x,y) -> P(s(x),y), \ALL x \ALL y. P(x,y) -> P(x,s(y)) :- P(s^n(0),s^n(0))
  def proof( k: Int, n: Int ) : LKProof =
  {
    if ( k == n )
    {
      val p1 = ForallLeftRule( upper_proof( 0, n ), assy_aux( n ), assy, Utils.numeral( n ) )
      WeakeningLeftRule( p1, assx )
    }
    else
    {
      val pk = Atom( p, Utils.numeral( k )::Utils.numeral( 0 )::Nil )
      val pkp1 = Atom( p, Utils.numeral( k + 1 )::Utils.numeral( 0 )::Nil )
      val impl = Imp( pk, pkp1 )

      ContractionLeftRule(
        ForallLeftRule(
          ForallLeftRule(
            ImpLeftRule(
              Axiom( pk::Nil, pk::Nil ),
              proof( k + 1, n ),
            pk, pkp1 ),
          impl, assx_aux( k ), Utils.numeral( 0 )),
        assx_aux( k ), assx, Utils.numeral( k )),
      assx )
    }
  }

  // returns LKProof with end-sequent  P(s^n(0),s^k(0)), \ALL y . P(s^n(0),y) -> P(s^n(0),s(y)) :- P(s^n(0),s^n(0))
  def upper_proof( k: Int, n: Int ) : LKProof =
  {
    if ( k == n ) // leaf proof
    {
      val a = Atom( p,  Utils.numeral( n )::Utils.numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), assy_aux( n ) )
    }
    else
    {
      val pk = Atom( p, Utils.numeral( n )::Utils.numeral( k )::Nil )
      val pkp1 = Atom( p, Utils.numeral( n )::Utils.numeral( k + 1 )::Nil )
      val impl = Imp( pk, pkp1 )

      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( pk::Nil, pk::Nil ), upper_proof( k + 1, n ), pk, pkp1 ), impl, assy_aux( n ), Utils.numeral( k ) ), assy_aux( n ))
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
object SquareEdges2DimExampleProof {
  //separate sucessor for the x- and y-directions
  val sx = "s_x"
  val sy = "s_y"
  //0 of the x-axis
  val a= "a"
  //0 of the y-axis
  val b = "b"

  val p = "P"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  //Converts integers into terms consisting of nested application of the successor function to 0
  def numeralX (n: Int) = Utils.iterateTerm(FOLConst( a ), sx, n)
  def numeralY (n: Int) = Utils.iterateTerm(FOLConst( b ), sy, n)

  val assx = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, Function( sx, x::Nil )::y::Nil ) ) ) )
  def assx_aux( k: Int ) = AllVar( y, Imp( Atom( p, numeralX(k)::y::Nil ), Atom(p, numeralX(k + 1)::y::Nil ) ) )

  val assy = AllVar( x, AllVar( y, Imp( Atom( p, x::y::Nil ), Atom(p, x::Function( sy, y::Nil )::Nil ) ) ) )
  def assy_aux( k: Int ) = AllVar( y, Imp( Atom( p, numeralX( k )::y::Nil ), Atom(p, numeralX( k )::Function( sy, y::Nil )::Nil ) ) )
 
  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(sx^k(a),0), \ALL x \ALL y. P(x,y) -> P(sx(x),y), \ALL x \ALL y. P(x,y) -> P(x,sy(y)) :- P(sx^n(a),sy^n(b))
  def proof( k: Int, n: Int ) : LKProof =
  {
    if ( k == n )
    {
      val p1 = ForallLeftRule( upper_proof( 0, n ), assy_aux( n ), assy, numeralX( n ) )
      WeakeningLeftRule( p1, assx )
    }
    else
    {
      val pk = Atom( p, numeralX(k)::numeralY(0)::Nil )
      val pkp1 = Atom( p, numeralX( k + 1)::numeralY(0)::Nil )
      val impl = Imp( pk, pkp1 )

      ContractionLeftRule(
        ForallLeftRule(
          ForallLeftRule(
            ImpLeftRule(
              Axiom( pk::Nil, pk::Nil ),
              proof( k + 1, n ),
            pk, pkp1),
          impl, assx_aux( k ), numeralY( 0 )),  //possibly not correct -> switch?
        assx_aux( k ), assx, numeralX( k )),    //same
      assx )
    }
  }

  // returns LKProof with end-sequent  P(s^n(0),s^k(0)), \ALL y . P(s^n(0),y) -> P(s^n(0),s(y)) :- P(s^n(0),s^n(0))
  //Conjecture: this is the part that goes in the Y-direction.
  def upper_proof( k: Int, n: Int ) : LKProof =
  {
    if ( k == n ) // leaf proof
    {
      val ax = Atom( p,  numeralX( n )::numeralY( n )::Nil )
      WeakeningLeftRule( Axiom( ax::Nil, ax::Nil ), assy_aux( n ) )
    }
    else
    {
      val pk = Atom( p, numeralX( n )::numeralY( k )::Nil )
      val pkp1 = Atom( p, numeralX( n )::numeralY( k + 1 )::Nil )
      val impl = Imp( pk, pkp1 )

      ContractionLeftRule(
        ForallLeftRule(
          ImpLeftRule(
            Axiom( pk::Nil, pk::Nil ),
            upper_proof( k + 1, n ),
            pk,
            pkp1),
          impl,
          assy_aux( n ),
          numeralY( k )), //possibly not correct: switch or maybe restructure.
        assy_aux( n ))
    }
  }
}


// Functions to construct the straightforward cut-free FOL LK proofs of the sequents
//
// P(s^n(0),0), \ALL x \ALL y . P(s(x),y) -> P(x,s(y)) :- P(0,s^n(0))
//
// where n is an Integer parameter >= 0.
object SumExampleProof {
  val s = "s"
  val p = "P"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  val ass = AllVar( x, AllVar( y, Imp( Atom( p, Function( s, x::Nil )::y::Nil ), Atom( p, x::Function( s, y::Nil )::Nil ) ) ) )
  def ass_inst( x: Int ) = AllVar( y, Imp( Atom( p, Function( s, Utils.numeral( x )::Nil )::y::Nil ), Atom( p, Utils.numeral( x )::Function( s, y::Nil )::Nil ) ) )
  def ass_inst_inst( x: Int, y: Int ) = Imp( Atom( p, Function( s, Utils.numeral( x )::Nil )::Utils.numeral( y )::Nil ), Atom( p, Utils.numeral( x )::Function( s, Utils.numeral( y )::Nil )::Nil ) )

  def apply( n: Int ) = proof( 0, n )

  // returns LKProof with end-sequent  P(s^{n-k}(0),s^k(0)), \ALL x \ALL y. P(s(x),y) -> P(x,s(y)) :- P(0,s^n(0))
  def proof( k: Int, n: Int )  : LKProof =
  {
    if ( k == n ) // leaf proof
    {
      val a = Atom( p, Utils.numeral( 0 )::Utils.numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val a1 = Atom( p, Utils.numeral( n - k )::Utils.numeral( k )::Nil )
      val a2 = Atom( p, Utils.numeral( n - (k + 1) )::Utils.numeral( k + 1 )::Nil )

      ContractionLeftRule(
        ForallLeftRule(
          ForallLeftRule(
            ImpLeftRule(
              Axiom( a1::Nil, a1::Nil ),
              proof( k + 1, n ),
            a1, a2 ),
          ass_inst_inst( n - (k + 1), k ), ass_inst( n - (k + 1) ), Utils.numeral( k ) ),
        ass_inst( n - (k + 1)), ass, Utils.numeral( n - (k + 1) ) ),
      ass )
    }
  }
}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// Refl, Trans, \ALL x. f(x) = x :- f^n(a) = a
//
// where n is an Integer parameter >= 0.
object LinearEqExampleProof {
  val a = "a"
  val f = "f"

  val x = FOLVar( "x")
  val y = FOLVar( "y")
  val z = FOLVar( "z")

  val Refl = AllVar( x, Equation(x ,x))
  val Ass = AllVar( x, Equation( Function( f, x::Nil ), x ))
  val Trans = AllVar( x, AllVar( y, AllVar( z, Imp( Equation(x, y), Imp( Equation(y, z), Equation(x, z) ) ) ) ) )

  def apply( n: Int ) = proof( n )

  // returns LKProof with end-sequent  Refl, Trans, \ALL x. f(x) = x :- f^k(a) = a
  def proof( k: Int )  : LKProof = {
    if ( k == 0 ) // leaf proof
    {
      val a_eq_a = Equation( Utils.iterateTerm( FOLConst( a ), f, 0 ), Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      WeakeningLeftRule( WeakeningLeftRule( ForallLeftRule( Axiom( a_eq_a::Nil, a_eq_a::Nil ), a_eq_a, Refl, FOLConst( a ) ), Trans ), Ass )
    }
    else
    {
      // atoms
      val ka_eq_a = Equation( Utils.iterateTerm( FOLConst( a ), f, k ), Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      val ka_eq_ka = Equation( Utils.iterateTerm( FOLConst( a ), f, k ), Utils.iterateTerm( FOLConst( a ), f, k ) )
      val kma_eq_a = Equation( Utils.iterateTerm( FOLConst( a ), f, k-1 ), Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      val ka_eq_kma = Equation( Utils.iterateTerm( FOLConst( a ), f, k ), Utils.iterateTerm( FOLConst( a ), f, k-1 ) )
      val ka_eq_z = Equation( Utils.iterateTerm( FOLConst( a ), f, k ), z )
      val kma_eq_z = Equation( Utils.iterateTerm( FOLConst( a ), f, k-1 ), z )
      val y_eq_z = Equation( y, z )
      val ka_eq_y = Equation( Utils.iterateTerm( FOLConst( a ), f, k ), y )
      val x_eq_y = Equation( x, y )
      val x_eq_z = Equation( x, z )
      
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
      val p3 = ForallLeftRule( p2, Trans3, Trans3_1, Utils.iterateTerm( FOLConst( a ), f, 0 ) )
      val p4 = ForallLeftRule( p3, Trans3_1, Trans3_2, Utils.iterateTerm( FOLConst( a ), f, k-1 ) )
      val p5 = ForallLeftRule( p4, Trans3_2, Trans3_3, Utils.iterateTerm( FOLConst( a ), f, k ) )

      val p6 = ForallLeftRule( p5, ka_eq_kma, Ass, Utils.iterateTerm( FOLConst( a ), f, k-1 ) )
     
      val p7 = ContractionLeftRule( p6, Ass )
      val p8 = ContractionLeftRule( p7, Trans )

      p8
    }
  }
}

object SumOfOnesF2ExampleProof {
  val s = "s"
  val zero = "0"
  val p = "+"
  var f = "f"

  val x = FOLVar( "x")
  val y = FOLVar( "y")
  val z = FOLVar( "z")

  //Helpers
  def Fn(n: Int) = Function(f, Utils.numeral(n)::Nil)

  //Forall x.(x + 1 = s(x)) (reversed to avoid the application of the symmetry of =)
  val Plus = AllVar(x, Equation(Function(p, x::Utils.numeral(1)::Nil), Function(s, x::Nil)))
  def PlusX(x:FOLTerm) = Equation(Function(p, x::Utils.numeral(1)::Nil),Function(s, x::Nil))

  //Forall xyz.(y=z -> (x+y=x+z))
  val EqPlus = AllVar(x, AllVar(y, AllVar(z, Imp(Equation( y, z), Equation(Function(p, y::x::Nil), Function(p, z::x::Nil)) ) )))
  def EqPlusX(x:FOLTerm) = AllVar(y, AllVar(z, Imp(Equation( y, z), Equation( Function(p, y::x::Nil), Function(p, z::x::Nil)) ) ))
  def EqPlusXY(x:FOLTerm, y:FOLTerm) = AllVar(z, Imp(Equation( y, z), Equation( Function(p, y::x::Nil), Function(p, z::x::Nil)) ) )
  def EqPlusXYZ(x:FOLTerm, y:FOLTerm, z:FOLTerm) = Imp(Equation( y, z), Equation( Function(p, y::x::Nil), Function(p, z::x::Nil)) )

  //Forall xyz.(x = y ^ y = z -> x = z)
  val Trans = AllVar(x, AllVar(y, AllVar(z, Imp(And(Equation( x, y) , Equation( y, z) ), Equation( x, z)))))

  //Definition of f
  //f(0) = 0
  val FZero = Equation(Function(f, Utils.numeral(0)::Nil), Utils.numeral(0))
  //Forall x.f(s(x)) = f(x) + s(0)
  val FSucc = AllVar(x, Equation( Function(f, Function(s, x::Nil)::Nil), Function(p, Function(f, x::Nil)::Utils.numeral(1)::Nil)))
  def FSuccX(x:FOLTerm) = Equation( Function(f, Function(s, x::Nil)::Nil), Function(p, Function(f, x::Nil)::Utils.numeral(1)::Nil))

  //The starting axiom f(n) = n |- f(n) = n
  def start(n: Int) = Axiom(Equation( Fn(n), Utils.numeral(n))::Trans::Plus::EqPlus::FSucc::Nil, Equation( Fn(n), Utils.numeral(n))::Nil)

  def apply(n: Int) = RecProof(start(n), n)

  /** Recursively constructs the proof, starting with the proof s1.
    */
  def RecProof(s1: LKProof, n: Int) : LKProof = {
    if (n <= 0) { s1 }
    else {

      val fn_eq_n = Equation( Fn(n-1), Utils.numeral(n-1))
      val fn_s0 = Function(p, Fn(n-1)::Utils.numeral(1)::Nil)
      val n_s0 = Function(p, Utils.numeral(n-1)::Utils.numeral(1)::Nil)

      val tr = TransRule(Fn(n), n_s0, Utils.numeral(n), s1)

      val tr2 = TransRule(Fn(n), fn_s0, n_s0, tr)

      val impl = ImpLeftRule(Axiom(fn_eq_n::Nil, fn_eq_n::Nil), tr2, fn_eq_n, Equation( fn_s0, n_s0))

      //Instantiate FSucc
      val allQFSucc = ForallLeftRule(impl, FSuccX(Utils.numeral(n-1)) , FSucc, Utils.numeral(n-1))
      val clFSucc = ContractionLeftRule(allQFSucc, FSucc)

      //Instantiate Plus
      val allQPlus = ForallLeftRule(clFSucc, PlusX(Utils.numeral(n-1)) , Plus, Utils.numeral(n-1))
      val clPlus = ContractionLeftRule(allQPlus, Plus)

      //Instantiare EqPlus (x=(s0), y=Fn(n-1), z=n-1)
      val eqx = Utils.numeral(1)
      val eqy = Fn(n-1)
      val eqz = Utils.numeral(n-1)

      val allQEqPlusZ = ForallLeftRule(clPlus, EqPlusXYZ(eqx, eqy, eqz) , EqPlusXY(eqx, eqy), eqz)
      val allQEqPlusYZ = ForallLeftRule(allQEqPlusZ, EqPlusXY(eqx, eqy) , EqPlusX(eqx), eqy)
      val allQEqPlusXYZ = ForallLeftRule(allQEqPlusYZ, EqPlusX(eqx) , EqPlus, eqx)
      val clEqPlus = ContractionLeftRule(allQEqPlusXYZ, EqPlus)

      RecProof(clEqPlus, n-1)
    }
  }
}


/** Constructs the cut-free FOL LK proof of the sequent
  * 
  * AUX, f(0) = 0, Forall x.f(s(x)) = f(x) + s(0) |- f(s^n(0)) = s^n(0)
  * Where AUX is {Transitivity, Symmetry, Reflexity of =,
  *               Forall xy.x=y -> s(x) = s(y), f(0) = 0, Forall x.f(s(x)) = f(x) + s(0)}
  */
object SumOfOnesFExampleProof {
  val s = "s"
  val zero = "0"
  val p = "+"
  var f = "f"

  val x = FOLVar( "x")
  val y = FOLVar( "y")
  val z = FOLVar( "z")

  //Helpers
  def Fn(n: Int) = Function(f, Utils.numeral(n)::Nil)

  //Forall xyz.(x = y ^ y = z -> x = z)
  val Trans = AllVar(x, AllVar(y, AllVar(z, Imp(And(Equation( x, y) , Equation( y, z) ), Equation( x, z)))))

  //Forall xy.(x=y -> s(x) = s(y))
  val CongSucc = AllVar(x, AllVar(y, Imp( Equation( x, y), Equation( Function(s, x::Nil), Function(s, y::Nil)))))
  def CongSuccX(x:FOLTerm) = AllVar(y, Imp( Equation( x, y), Equation( Function(s, x::Nil), Function(s, y::Nil))))
  def CongSuccXY(x:FOLTerm, y:FOLTerm) = Imp( Equation( x, y), Equation(Function(s, x::Nil), Function(s, y::Nil)))

  //Forall x.(x + 1 = s(x)) (reversed to avoid the application of the symmetry of =)
  val Plus = AllVar(x, Equation( Function(p, x::Utils.numeral(1)::Nil), Function(s, x::Nil)))
  def PlusX(x:FOLTerm) = Equation( Function(p, x::Utils.numeral(1)::Nil), Function(s, x::Nil))

  //Definition of f
  //f(0) = 0
  val FZero = Equation( Function(f, Utils.numeral(0)::Nil), Utils.numeral(0))
  //Forall x.f(s(x)) = f(x) + s(0)
  val FSucc = AllVar(x, Equation( Function(f, Function(s, x::Nil)::Nil), Function(p, Function(f, x::Nil)::Utils.numeral(1)::Nil)))
  def FSuccX(x:FOLTerm) = Equation( Function(f, Function(s, x::Nil)::Nil), Function(p, Function(f, x::Nil)::Utils.numeral(1)::Nil))


  //The starting axiom f(n) = n |- f(n) = n
  def start(n: Int) = Axiom(Equation( Fn(n), Utils.numeral(n))::Trans::Plus::CongSucc::FSucc::Nil, Equation( Fn(n), Utils.numeral(n))::Nil)

  def apply(n: Int) = proof(n)
  def proof (n: Int) = TermGenProof(EqChainProof(start(n), n), 0, n)

  /** Generates a sequent containing, in addition to the formulas in the bottommost sequent of s1,
    * the chain of equations f(n) = s(f(n-1)),...,f(1)=s(f(0)), f(0) = 0.s
    * The generates proof employs only the axiom of transitivity and (x=y -> s(x) = s(y)))
    *
    * TODO should be private - but scala shell does not allow access modifiers when :loading a file
    */
  def EqChainProof (s1: LKProof,  n: Int) : LKProof = {
    if (n <= 0) { s1 }
    else {
      val tr = TransRule(Fn(n), Utils.iterateTerm(Fn(n-1), s, 1), Utils.numeral(n), s1)

      val ax2 = Axiom(Equation( Fn(n-1), Utils.numeral(n-1))::Nil, Equation( Fn(n-1), Utils.numeral(n-1))::Nil)

      //Introduces the instantiated form of CongSuc
      val impl = ImpLeftRule(ax2, tr, Equation( Fn(n-1), Utils.numeral(n-1)), Equation( Utils.iterateTerm(Fn(n-1), s, 1), Utils.numeral(n)))

      //Quantify CongSucc
      val cong1 = ForallLeftRule(impl, CongSuccXY(Fn(n-1), Utils.numeral(n-1)), CongSuccX(Fn(n-1)), Utils.numeral(n-1))
      val cong2 = ForallLeftRule(cong1, CongSuccX(Fn(n-1)), CongSucc, Fn(n-1))

      val cl = ContractionLeftRule(cong2, CongSucc)

      EqChainProof(cl, n-1)
    }
  }

  /** Given a proof s1, produced by EqChainProof, generates a proof that
    * eliminates the chains of equasions and proves the final sequent
    * FZero, FSucc, TR, Plus |- f(n) = n.
    *
    * TODO should be private - but scala shell does not allow access modifiers when :loading a file
    */
  def TermGenProof (s1: LKProof, n: Int, targetN: Int) : LKProof = {
    if (n >= targetN) { s1 }
    else {

      val tr = TransRule(Fn(n+1), Function(p, Fn(n)::Utils.numeral(1)::Nil), Utils.iterateTerm(Fn(n), s, 1), s1)

      //Quantify plus
      val plus = ForallLeftRule(tr, PlusX(Fn(n)), Plus, Fn(n))
      val clPlus = ContractionLeftRule(plus, Plus)

      //Quantify fsucc
      val fsucc = ForallLeftRule(clPlus, FSuccX(Utils.numeral(n)), FSucc, Utils.numeral(n))
      val clFSucc = ContractionLeftRule(fsucc, FSucc)

      TermGenProof(clFSucc, n+1, targetN)
    }

  }


}

// Functions to construct cut-free FOL LK proofs of the sequents
//
// Refl, Trans, CongSuc, ABase, ASuc, :- sum( n ) = s^n(0)
//
// where n is an Integer parameter >= 0.
object SumOfOnesExampleProof {
  val s = "s"
  val zero = "0"
  val p = "+"

  val x = FOLVar( "x")
  val y = FOLVar( "y")
  val z = FOLVar( "z")

  // axioms
  val Refl = AllVar( x, Equation( x, x ))
  val Trans = AllVar( x, AllVar( y, AllVar( z, Imp( Equation( x, y ), Imp( Equation( y, z ), Equation( x, z ) ) ) ) ) )
  val CongSuc = AllVar( x, AllVar( y, Imp( Equation( x, y ),
  Equation( Function( s, x::Nil ), Function( s, y::Nil )) ) ) )
  val ABase = AllVar( x, Equation(Function( p, x::FOLConst( zero )::Nil ), x ) )
  val ASuc = AllVar( x, AllVar( y, Equation( Function( p, x::Function( s, y::Nil )::Nil ), Function( s, Function( p, x::y::Nil )::Nil ) ) ) )

  def apply( n: Int ) = proof( n )

  // TODO should be private - but scala shell does not allow access modifiers when :loading a file
  def proof( k: Int ) : LKProof = {
    if ( k == 0 )
    {
      val zero_eq_zero = Equation( Utils.numeral( 0 ), Utils.numeral( 0 ) )
      val p1 = ForallLeftRule( Axiom( zero_eq_zero::Nil, zero_eq_zero::Nil ), zero_eq_zero, Refl, Utils.numeral( 0 ) )
      val p2 = WeakeningLeftRule( p1, Trans )
      val p3 = WeakeningLeftRule( p2, CongSuc )
      val p4 = WeakeningLeftRule( p3, ABase )
      WeakeningLeftRule( p4, ASuc )
    }
    else if ( k == 1 )
    {
      val one_eq_one = Equation( Utils.numeral( 1 ), Utils.numeral( 1 ) )
      val p1 = ForallLeftRule( Axiom( one_eq_one::Nil, one_eq_one::Nil ), one_eq_one, Refl, Utils.numeral( 1 ) )
      val p2 = WeakeningLeftRule( p1, Trans )
      val p3 = WeakeningLeftRule( p2, CongSuc )
      val p4 = WeakeningLeftRule( p3, ABase )
      WeakeningLeftRule( p4, ASuc )
    }
    else
    {
      /// atoms
      val ssumkm1_eq_k = Equation( Function( s, sum( k-1 )::Nil ), Utils.numeral( k ) )
      val ssumkm1_eq_z = Equation( Function( s, sum( k-1 )::Nil ), z )
      val sumk_eq_k = Equation( sum( k ), Utils.numeral( k ) )
      val sumk_eq_y = Equation( sum( k ), y )
      val sumk_eq_z = Equation( sum( k ), z )
      val y_eq_z = Equation( y, z )
      val sumk_eq_ssumkm1 = Equation( sum( k ), Function( s, sum( k-1 )::Nil ) )
      val sumkm1_eq_km1 = Equation( sum( k-1 ), Utils.numeral( k-1 ) )
      val sumkm1_eq_y = Equation( sum( k-1 ), y )
      val ssumkm1_eq_sy = Equation( Function( s, sum( k-1 )::Nil ), Function( s, y::Nil ) )
      
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
      val p6 = ForallLeftRule( p5, Trans3, Trans3_1, Utils.numeral( k ) )
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
      val p16 = ForallLeftRule( p15, CongSuc2, CongSuc2_1, Utils.numeral( k-1 ) )
      val p17 = ForallLeftRule( p16, CongSuc2_1, CongSuc, sum( k-1 ) )
      ContractionLeftRule( p17, CongSuc )
    }
  }

  // constructs proof of: Trans, CongSuc, ASuc, ABase :- sum( k + 1 ) = s( sum( k ) )
  // TODO should be private - but scala shell does not allow access modifiers when :loading a file
  def aux_proof( k: Int ) : LKProof = {
    /// atoms
    val ssumkp0_eq_ssumk = Equation( Function( s, Function( p, sum( k )::Utils.numeral( 0 )::Nil )::Nil ), Function( s, sum( k )::Nil ) )
    val sumkp1_eq_ssumk = Equation( sum( k+1 ), Function( s, sum( k )::Nil ) )
    val sumkp1_eq_ssumkp0 = Equation( sum( k+1 ), Function( s, Function( p, sum( k )::Utils.numeral( 0 )::Nil )::Nil ) )
    val ssumkp0_eq_z = Equation( Function( s, Function( p, sum( k )::Utils.numeral( 0 )::Nil )::Nil ), z )
    val sumkp1_eq_z = Equation( sum( k+1 ), z )
    val sumkp1_eq_y = Equation( sum( k+1 ), y )
    val y_eq_z = Equation( y, z )
    val sumkp0_eq_sumk = Equation( Function( p, sum( k )::Utils.numeral( 0 )::Nil ), sum( k ) )
    val sumkp0_eq_y = Equation( Function( p, sum( k )::Utils.numeral( 0 )::Nil ), y )
    val ssumkp0_eq_sy = Equation( Function( s, Function( p, sum( k )::Utils.numeral( 0 )::Nil )::Nil ), Function( s, y::Nil ) )
    val sumkpsy_eq_ssumkpy = Equation( Function( p, sum( k )::Function( s, y::Nil)::Nil ), Function( s, Function( p, sum( k )::y::Nil )::Nil ) )
 
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
    val p7 = ForallLeftRule( p6, Trans3_1, Trans3_2, Function( s, Function( p, sum( k )::Utils.numeral( 0 )::Nil )::Nil ) )
    val p8 = ForallLeftRule( p7, Trans3_2, Trans, sum( k+1 ) )

    // congruence sucessor
    val p9 = Axiom( sumkp0_eq_sumk::Nil, sumkp0_eq_sumk::Nil )
    val p10 = ImpLeftRule( p9, p8, sumkp0_eq_sumk, ssumkp0_eq_ssumk )
    val p11 = ForallLeftRule( p10, Cong2, Cong2_1, sum( k ) )
    val p12 = ForallLeftRule( p11, Cong2_1, CongSuc, Function( p, sum( k )::Utils.numeral( 0 )::Nil ) )

    // addition sucessor case
    val p13 = ForallLeftRule( p12, sumkp1_eq_ssumkp0, ASuc_1, Utils.numeral( 0 ) )
    val p14 = ForallLeftRule( p13, ASuc_1, ASuc, sum( k ) )

    // addition base case
    ForallLeftRule( p14, sumkp0_eq_sumk, ABase, sum( k ) )
  }

  // the term (.((1 + 1) + 1 ) + ... + 1 ), k must be at least 1
  // TODO should be private - but scala shell does not allow access modifiers when :loading a file
  def sum( k: Int ) : FOLTerm = {
    if ( k == 1 )  Utils.numeral( 1 )
    else           Function( p, sum( k-1 )::Utils.numeral( 1 )::Nil )
  }
}



/**
 * Auxiliary structure to deal with axioms of the schema:
 * Forall variables cond1 -> cond2 -> ... -> condn -> consequence |- ...
 */
class AllQuantifiedConditionalAxiomHelper(variables: List[FOLVar], conditions: List[FOLFormula], consequence: FOLFormula) {
  /**
   * Returns the full axiom
   */
  def get_axiom(): FOLFormula = {
    // TODO: refactor apply_conditional_equality, combine duplicate code
    var impl_chain = consequence
    for (elem <- conditions.reverse) {
      impl_chain = Imp(elem, impl_chain)
    }

    def quantify(variables: List[FOLVar], body: FOLFormula): FOLFormula = {
      variables match {
        case Nil => body
        case head :: tail => AllVar(head, quantify(tail, body))
      }
    }

    quantify(variables, impl_chain)
  }

  /**
   * Use axiom with given expressions in proof.
   * Consequence of axiom must appear in current proof.
   * Instantiated conditions will of course remain in the antecedent of the returned proof
   */
  def apply(expressions: List[FOLTerm], p: LKProof): LKProof = {
    assert(expressions.length == variables.length, "Number of expressions doesn't equal number of variables")

    // construct implication with instantiated conditions and consequence
    var instantiated_conditions = conditions
    var instantiated_consequence = consequence
    for (i <- 0 to variables.length - 1) {
      val substitute = (x: FOLFormula) => Substitution(variables(i), expressions(i))(x)
      instantiated_conditions = instantiated_conditions.map(substitute)
      instantiated_consequence = substitute(instantiated_consequence)
    }

    val p1 = apply_conditional_equality(instantiated_conditions, instantiated_consequence, p)

    // iteratively instantiate all-quantified variables with expression
    def instantiate_axiom(expressions: List[FOLTerm], axiom: FOLFormula, p: LKProof): LKProof = {
      expressions match {
        case Nil => p
        case head :: tail => {
          val new_axiom = instantiate(axiom, head)
          val new_p = instantiate_axiom(tail, new_axiom, p)

          ForallLeftRule(new_p, new_axiom, axiom, head)
        }
      }
    }

    val ax = get_axiom()
    val p2 = instantiate_axiom(expressions, ax, p1)

    ContractionLeftRule(p2, ax)
  }

  private def apply_conditional_equality(equalities: List[FOLFormula], result: FOLFormula, p: LKProof) : LKProof = {
    equalities match {
      case Nil => {
        p // no conditions at all
      }
      case head :: Nil => {
        val ax = Axiom(head::Nil, head::Nil)
        ImpLeftRule(ax, p, head, result)
      }
      case head :: tail => {
        val ax = Axiom(head::Nil, head::Nil)
        var impl_chain = result
        for (elem <- tail.reverse) {
          impl_chain = Imp(elem, impl_chain)
        }
        val s2 = apply_conditional_equality(tail, result, p)
        ImpLeftRule(ax, s2, head, impl_chain)
      }
    }
  }
}

object UniformAssociativity3ExampleProof {

  val s = "s"
  val p = "+"

  val x = FOLVar( "x")
  val y = FOLVar( "y")
  val z = FOLVar( "z")

  val x1 = FOLVar( "x_1")
  val x2 = FOLVar( "x_2")
  val y1 = FOLVar( "y_1")
  val y2 = FOLVar( "y_2")

  def f1( sym: String, arg: FOLTerm ) = Function(sym, arg::Nil)
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ) : FOLTerm = Function(sym, arg1::arg2::Nil)
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ) : FOLTerm = f2(sym, arg1, arg2)

  // Axioms

  // Trans as from TransRule, possibly unify or generalise
  val Trans = AllVar(x, AllVar(y, AllVar(z, Imp(And(Equation( x, y) , Equation( y, z) ), Equation( x, z)))))
  val Symm = AllVar(x, Equation( x, x))
  val Cs = AllVar(x, AllVar(y, Imp(Equation( x, y), Equation( Function(s, x::Nil), Function(s, y::Nil)))))

  // TODO: port these axioms to new format using AllQuantifiedConditionalAxiomHelper
  def refl_ax(): FOLFormula = AllVar(x, refl_ax(x))
  def refl_ax(x: FOLTerm): FOLFormula = AllVar(y, refl_ax(x, y))
  def refl_ax(x: FOLTerm, y: FOLTerm): FOLFormula = Imp(Equation( x, y), Equation( y, x))

  // x=y -> s(x) = s(y)
  def cs_ax(): FOLFormula = AllVar(x, cs_ax(x))
  def cs_ax(x: FOLTerm): FOLFormula = AllVar(y, cs_ax(x, y))
  def cs_ax(x: FOLTerm, y: FOLTerm): FOLFormula = Imp(Equation( x, y), Equation( Function(s, x::Nil), Function(s, y::Nil)))
  
  // x1 = x2 -> y1 = y2 -> x1 + y1 = x2 + y2
  val cp = new AllQuantifiedConditionalAxiomHelper(x1::x2::y1::y2::Nil, Equation( x1, x2)::Equation(y1, y2)::Nil, Equation(Function(p, x1::y1::Nil), Function(p, x2::y2::Nil)))

  // Arithmetic axioms
  val Ax1 = AllVar(x, Equation(Function(p, x::Utils.numeral(0)::Nil), x))

  // Forall x, y: s(x+y) = x+s(y)
  def ax2_ax(): FOLFormula = AllVar(x, AllVar(y, ax2_ax(x, y) ))
  def ax2_ax(x: FOLTerm): FOLFormula = AllVar(y, ax2_ax(x, y) )
  def ax2_ax(x: FOLTerm, y: FOLTerm): FOLFormula = Equation( f1(s, f2(x, p, y)), f2( x, p, f1(s, y)) )

  def apply(n: Int): LKProof = {
    assert (n>=1, "n must be >= 1")
    val p = gen_proof_step(0, n)
    induction_start(n, p)
  }

  /**
   * Close off proof ending in (n + n) + 0 = n + (n + 0) |- ...
   */
  def induction_start(n: Int, p0: LKProof): LKProof = {
    // show both sides equal to n + n
    val n_num = Utils.numeral(n)
    val zero = Utils.numeral(0)
    val c1 = f2(f2(n_num, p, n_num), p, zero)
    val d1 = f2(n_num, p, n_num)
    val e1 = f2(n_num, p, f2(n_num, p, zero))
    val p1 = TransRule(c1, d1, e1, p0)

    // show (n + n) + 0 = (n + n) directly via ax1
    val p2 = ForallLeftRule(p1, Equation( c1, d1), Ax1, d1)
    val p3 = ContractionLeftRule(p2, Ax1)

    // show (n + n) = n + (n + 0) 
    val p4 = cp(n_num::n_num::n_num::f2(n_num, p, zero)::Nil, p3)

    // show n = n and n = n + 0
    val p5 = ForallLeftRule(p4, Equation( n_num, n_num), Symm, n_num)
    val p6 = ContractionLeftRule(p5, Symm)

    val p7 = reflect(f2(n_num, p, zero), n_num, p6)

    val p8 = ForallLeftRule(p7, Equation( f2(n_num, p, zero), n_num), Ax1, n_num)
    ContractionLeftRule(p8, Ax1)
  }

  /***
    * Returns proof Pi (currently including line above and below Pi), with numerals n, i, i+1:
    * (n + n) + i+1 = n + (n + i+1), Ax |- ...
    *  Pi
    * (n + n) + i   = n + (n + i), Ax |- ...
    */
  def gen_proof_step(i: Int, n: Int) : LKProof = {
    val n_num = Utils.numeral(n)
    val i_num = Utils.numeral(i)
    val ip1_num = Utils.numeral(i+1)

    val a1 = f2( f2( n_num, p, n_num ), p, ip1_num )
    val a2 = f2( n_num, p, f2( n_num, p, ip1_num ) )
    val b1 = f2( n_num, p, f1(s, f2( p, n_num, i_num ) ) )

    val p0 =
      if (i+1 >= n) {
        // start, add axioms
        val all_axioms = Trans::cp.get_axiom()::Symm::ax2_ax()::cs_ax()::refl_ax()::Ax1::Nil
        def add_ax(start: LKProof, axioms : List[FOLFormula]): LKProof = {
          axioms match {
            case Nil => start
            case head::tail => WeakeningLeftRule(add_ax(start, tail), head)
          }
        }

        val final_expression = Equation( a1, a2 )

        val top = Axiom( final_expression::Nil, final_expression::Nil )
        add_ax(top, all_axioms)
      } else {
        gen_proof_step(i+1, n)
      }

    val p1 = TransRule(a1, b1, a2, p0)

    // the left side now contains
    // (n + n) + s(i) = n + s(n + i) as well as
    // n + s(n + i) = n + (n + s(i))

    // use Cp to reduce the latter to s(n + i) = (n + s(i))
    val x1_1 = n_num
    val x2_1 = n_num
    val y1_1 = f1(s, f2( n_num, p, i_num ))
    val y2_1 = f2(n_num, p, f1(s, i_num))
    val p8 = cp(x1_1::x2_1::y1_1::y2_1::Nil, p1)

    // show x1 = x2 by symmetry
    val p9 = ForallLeftRule(p8, Equation( x1_1, x2_1 ), Symm, n_num)
    val p10 = ContractionLeftRule(p9, Symm)

    // show y1 = y2 by Ax2 (i.e. s(n + i) = (n + s(i)) )
    val p13 = show_by_ax2(n_num, i_num, p10)

    // now we only have (n + n) + s(i) = n + s(n + i) left (c=e), reduce right hand side by Ax2 and Trans to s(n + (n + i) (c=d) )
    val c1 = f2(f2(n_num, p, n_num), p, f1(s, i_num))
    val d1 = f1(s, f2(n_num, p, f2(n_num, p, i_num)))
    val e1 = f2(n_num, p, f1(s, f2(n_num, p, i_num)))
    val p14 = TransRule(c1, d1, e1, p13)

    // show d=e by Ax2
    val p15 = show_by_ax2(n_num, f2(n_num, p, i_num), p14)

    // next goal: reduce (n + n) + s(i) = s(n + (n + i) to (n + n) + s(i) = s( (n + n) + i) using the IH, Trans and Cs)
    val c2 = f2(f2(n_num, p, n_num), p, f1(s, i_num))
    val d2 = f1(s, f2(f2(n_num, p, n_num), p, i_num))
    val e2 = d1
    val p16 = TransRule(c2, d2, e2, p15)

    val p17 = show_by_cs(f2(f2(n_num, p, n_num), p, i_num), f2(n_num, p, f2(n_num, p, i_num)), p16)

    // now we have:
    // (n + n) + s(i) = s( (n + n) + i) 
    // as well as
    // (n + n) + i = n + (n + i)
    // -> use Ax2

    // use reflection to match definition of ax2 afterwards
    val p18 = reflect( d2, c2, p17 )

    val p19 = show_by_ax2( f2(n_num, p, n_num), i_num, p18)
    p19

    // we end up with the IH (n + n) + i = n + (n + i)
  }

  def show_by_ax2(x: FOLTerm, y: FOLTerm, p: LKProof): LKProof = {
    val p1 = ForallLeftRule(p, ax2_ax(x, y), ax2_ax(x), y)
    val p2 = ForallLeftRule(p1, ax2_ax(x), ax2_ax(), x)
    ContractionLeftRule(p2, ax2_ax())
  }

  def show_by_cs(x: FOLTerm, y: FOLTerm, p: LKProof): LKProof = {
    val p1 = apply_conditional_equality( Equation( x, y)::Nil, Equation( Function(s, x::Nil), Function(s, y::Nil)), p)

    val p2 = ForallLeftRule(p1, cs_ax(x, y), cs_ax(x), y)
    val p3 = ForallLeftRule(p2, cs_ax(x), cs_ax(), x)
    ContractionLeftRule(p3, cs_ax())
  }

  /**
    * Takes a proof s2 with end-sequent of the form
    * (x=y), ... |- ...
    * and return one with end-sequent of the form
    * (y=x), ... |- ...
    */
  def reflect(x: FOLTerm, y: FOLTerm, p: LKProof): LKProof = {
    val p1 = apply_conditional_equality( Equation(x,y)::Nil, Equation(y,x), p)

    val p2 = ForallLeftRule(p1, refl_ax(x, y), refl_ax(x), y)
    val p3 = ForallLeftRule(p2, refl_ax(x), refl_ax(), x)
    ContractionLeftRule(p3, refl_ax())
  }

  def apply_conditional_equality(equalities: List[FOLFormula], result: FOLFormula, p: LKProof) : LKProof = {
    equalities match {
      case Nil => p
      case head :: Nil => {
        val ax = Axiom(head::Nil, head::Nil)
        ImpLeftRule(ax, p, head, result)
      }
      case head :: tail => {
        val ax = Axiom(head::Nil, head::Nil)
        var impl_chain = result
        for (elem <- tail.reverse) {
          impl_chain = Imp(elem, impl_chain)
        }
        val s2 = apply_conditional_equality(tail, result, p)
        ImpLeftRule(ax, s2, head, impl_chain)
      }
    }
  }
}



/**
 * Proof of f(n) = g(n, 1), where f is the head recursive and g the tail recursive formulation of the factorial function
 */
object FactorialFunctionEqualityExampleProof {

  val p = "+"
  val m = "*"
  val s = "s"
  val f = "f"
  val g = "g"

  val x = FOLVar("x")
  val y = FOLVar("y")
  val z = FOLVar("z")

  def f1( sym: String, arg: FOLTerm ) = Function(sym, arg::Nil)
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ) : FOLTerm = Function(sym, arg1::arg2::Nil)
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ) : FOLTerm = f2(sym, arg1, arg2)

  val f_ax_1 = Equation( f1(f, Utils.numeral(0)), f1(s, Utils.numeral(0)))
  val f_ax_2 = parse.fol("Forall x =(f(s(x)), *(s(x) , f(x)))")

  val g_ax_1 = new AllQuantifiedConditionalAxiomHelper(y::Nil, Nil, Equation( y, f2(g, Utils.numeral(0), y)))
  val g_ax_2 = parse.fol("Forall x Forall y =( g(s(x), y), g(x, *(y , s(x))) )")

  val g_compat_2 = new AllQuantifiedConditionalAxiomHelper(x::y::z::Nil, Equation( y, z)::Nil, Equation( f2(g, x, y), f2(g, x, z)))

  val trans_axiom = new AllQuantifiedConditionalAxiomHelper(x::y::z::Nil, Equation( x, y)::Equation( y, z)::Nil, Equation( x, z))
  val symm_axiom = AllVar(x, Equation( x, x))
  val refl_axiom = new AllQuantifiedConditionalAxiomHelper(x::y::Nil, Equation( x, y)::Nil, Equation( y, x))
  val compat_mul_axiom = new AllQuantifiedConditionalAxiomHelper(x::y::z::Nil, Equation( x, y)::Nil, Equation( f2(z, m, x), f2(z, m, y)))
  val assoc_mul_axiom = new AllQuantifiedConditionalAxiomHelper(x::y::z::Nil, Nil, Equation( f2(x, m, f2(y, m, z)), f2(f2(x, m, y), m, z)))

  val mul_neutral_axiom = new AllQuantifiedConditionalAxiomHelper(x::Nil, Nil, Equation( f2(x, m, Utils.numeral(1)), x))
  // this second axiom saves us from adding commutativity of multiplication
  val mul_neutral_axiom_2 = new AllQuantifiedConditionalAxiomHelper(x::Nil, Nil, Equation( f2(Utils.numeral(1), m, x), x))

  def apply(n :Int): LKProof = induction_steps(n)

  def induction_steps(n: Int): LKProof = {
    val axiom_formulae = Equation( f1(f, Utils.numeral(n)), f2(g, Utils.numeral(n), Utils.numeral(1)))::Nil
    val axiom : LKProof = Axiom(axiom_formulae, axiom_formulae)

    // add axioms
    val all_axioms = List[FOLFormula](f_ax_1, f_ax_2, g_ax_1.get_axiom(), g_ax_2, symm_axiom, refl_axiom.get_axiom(),
      trans_axiom.get_axiom(), compat_mul_axiom.get_axiom(), assoc_mul_axiom.get_axiom(), g_compat_2.get_axiom(),
      mul_neutral_axiom.get_axiom(), mul_neutral_axiom_2.get_axiom())
    val p1 = all_axioms.foldLeft( axiom )( (proof, elem) => WeakeningLeftRule(proof, elem))

    val n_num = Utils.numeral(n)

    /**
     * Returns (( ([start_value*]n)*(n-1) ) * ... * ) k
     */
    def get_partial_factorial_term(n: Int, k: Int, start_value: Option[FOLTerm] = None): FOLTerm = {
      if (n <= k) {
        if (n == k) {
          start_value match {
            case Some(value) => f2(value, m, Utils.numeral(n))
            case None => Utils.numeral(n)
          }
        } else throw new Exception("k larger than n in partial factorial")
      } else {
        f2(m, get_partial_factorial_term(n, k+1, start_value), Utils.numeral(k))
      }
    }

    def induction_step_rec(p0: LKProof, k: Int): LKProof = {

      val k_num = Utils.numeral(k)
      val zero = Utils.numeral(0)
      val one = Utils.numeral(1)

      val part_fac =   if (n==k) one else  get_partial_factorial_term(n, k+1)
      val part_fac_next = get_partial_factorial_term(n, k)

      val f_k_term = if (n == k) f1(f, k_num)               // f(k)
                     else f2(m, part_fac, f1(f, k_num))     // part_fac * f(k)

      val g_k_term =  f2(g, k_num, part_fac)

      if (k == 0)  {
        // we have: n! * f(0) = g(0, ( ... (( (1 * n) * (n-1) ) * (n-2) ) * ... ) * 1 )

        // use f(0) = s(0)
        val p1 = trans_axiom( List( f_k_term, f2(part_fac, m, f1(s, zero)), g_k_term), p0 )
        val p2 = compat_mul_axiom( List( f1(f, zero), f1(s, zero), part_fac), p1 )
        val p3 = ContractionLeftRule( p2, f_ax_1 )

        // use g(0, y) = y
        val p4 = trans_axiom( List(f2(part_fac, m, f1(s, zero)), part_fac, g_k_term), p3)
        val p5 = g_ax_1( part_fac::Nil, p4 )

        // the formula actually says n! * 1 = n!, we have to get rid of the 1
        val p6 = trans_axiom( List(f2(part_fac, m, one), part_fac, part_fac), p5 )
        val p7 = mul_neutral_axiom( List(part_fac), p6)
        val p8 = ForallLeftRule(p7, Equation( part_fac, part_fac), symm_axiom, part_fac)
        val p9 = ContractionLeftRule(p8, symm_axiom)

        p9
      } else {
        // lhs contains part_fac * f(k) = g(k, part_fac)

        val km1_num = Utils.numeral(k-1) // must not be evaluated for k == 0
        val f_km1_term = f2(m, part_fac_next, f1(f, km1_num)) // (part_fac * k) * f(k-1)
        val g_km1_term = f2(g, km1_num, part_fac_next)

        // first step: decompose f: part_fac * k * f(k-1) = g(k, 1*part_fac)
        val p1 = trans_axiom( List(f_k_term, f_km1_term, g_k_term), p0)

        val p3 =
          if (n==k) {
            // use axiom directly, part_fac is empty
            val p1_0 = ForallLeftRule(p1, Equation( f_k_term, f_km1_term), f_ax_2, km1_num)
            ContractionLeftRule(p1_0, f_ax_2)
          } else  {
            // the antecedent contains something along the lines of:
            // 4*f(3) = (4*3) * f(2) or
            // (4*3)*f(2) = ((4*3)*2) * f(1)
            // we however need the last part exposed and grouped to be able to use compat & f_ax2 to show it, like in: 4*f(3) = 4* (3*f(2))
            // use Trans to expose it and show it, other part can be shown by associativity
            // step in between (=yTrans):
            // 4 * (3*f(2)) or
            // (4*3) * (2*f(1))
            val yTrans = f2(part_fac, m, f2(k_num, m, f1(f, km1_num)))
            val p1_0 = trans_axiom( f_k_term::yTrans::f_km1_term::Nil, p1)
            // show by compat, then f_ax_2: part_fac * f(k) = part_fac * (k * f(k-1))
            val f_k = f1(f, k_num)
            val k_f_km1 = f2(k_num, m, f1(f, km1_num))
            val p1_1 = compat_mul_axiom( List(f_k, k_f_km1, part_fac), p1_0)
            val p1_2 = ForallLeftRule(p1_1, Equation( f_k, k_f_km1), f_ax_2, km1_num)
            val p1_3 = ContractionLeftRule(p1_2, f_ax_2)
            // show by assoc: part_fac * (k * f(k-1)) = (part_fac * k) * f(k-1)
            val p1_4 = assoc_mul_axiom( List(part_fac, k_num, f1(f, km1_num)), p1_3)
            p1_4
        }

        // now transform k * f(k-1) = g(k, part_fac) to k * f(k-1) = g(k-1, part_fac * k)
        val p4 = trans_axiom( List(f_km1_term, g_km1_term, g_k_term), p3)

        // show g(k, part_fac) = g(k-1, part_fac*k) (need to use reflection to get to this form first)
        val p4_2 = refl_axiom( g_k_term::g_km1_term::Nil, p4 )

        val p5 =
          if (n==k) {
            // g is initially called with a 1 as second argument, but we want to get rid of it to make the final result equal to the one f produces
            // use trans to split into g-axiom part and part where the two expressions only differ by this extra one
            val g_intermed = f2(g, km1_num, f2(one, m, part_fac_next))
            val p5_1 = trans_axiom( g_k_term::g_intermed::g_km1_term::Nil, p4_2 )
            // show g(n, 1) = g(n-1, 1*n) by g_ax_2
            val intermed = AllVar(y, Equation( f2(g, k_num, y), f2(g, km1_num, f2(y, m, k_num))))
            val p5_2 = ForallLeftRule(p5_1, Equation( g_k_term, g_intermed), intermed, one)
            val p5_3 = ForallLeftRule(p5_2, intermed, g_ax_2, km1_num)
            val p5_4 = ContractionLeftRule(p5_3, g_ax_2)

            // show g(n-1, 1*n) = g(n-1, n) by g_compat_2
            val p5_5 = g_compat_2( List(km1_num, f2(one, m, k_num), k_num), p5_4)
            // show 1 * k = k
            val p5_6 = mul_neutral_axiom_2( List(k_num), p5_5 )
            p5_6
          } else {
            val intermed = AllVar(y, Equation( f2(g, f1(s, km1_num), y), f2(g, km1_num, f2(m, y, f1(s, km1_num)))))
            val p6 = ForallLeftRule(p4_2, Equation( g_k_term, g_km1_term), intermed, part_fac)
            val p7 = ForallLeftRule(p6, intermed, g_ax_2, km1_num)
            val p8 = ContractionLeftRule(p7, g_ax_2)
            p8
          }

        induction_step_rec(p5, k-1)
      }
    }

    induction_step_rec(p1, n)
  }
}
