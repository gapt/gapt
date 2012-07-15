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


// Constructs the set of FOLTerms { 0, s(0), s(s(0)), ..., s^n(0) }

object LinearExampleTermset
{ 
  def apply( n: Int ) : List[FOLTerm] =
    if ( n == 0 )
      List[FOLTerm]()
    else
      Numeral( n - 1 ) :: apply( n - 1)
}


// Constructs the FOLTerm s^k(0)

object Numeral
{
  val s = new ConstantStringSymbol("s")

  def apply( k: Int ) : FOLTerm =
    if ( k == 0 )
      FOLConst( new ConstantStringSymbol("0") )
    else
      Function( s, apply( k - 1 )::Nil )
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
