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

object CutIntroExampleProof
{
  val s = new ConstantStringSymbol("s")
  val p = new ConstantStringSymbol("P")
  val c = new ConstantStringSymbol("0")

  def apply( n: Int ) = proof( 0, n )

  def proof( k: Int, n: Int )  : LKProof =
  {
    val x = FOLVar( VariableStringSymbol("x") )
    val ass = AllVar( x, Imp( Atom( p, x::Nil ), Atom( p, Function( s, x::Nil )::Nil ) ) )
    if ( k == n ) // Leaf proof
    {
      val a = Atom( p,  SuccTerm( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val p1 = Atom( p, SuccTerm( k )::Nil )
      val p2 = Atom( p, SuccTerm( k + 1 )::Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1::Nil, p1::Nil ), proof( k + 1, n ), p1, p2 ), aux, ass, SuccTerm( k ) ), ass )
    }
  }

}

// Constructs the set of FOLTerms { 0, s(0), s(s(0)), ..., s^n(0) }

object CutIntroExampleTermset
{ 
  def apply( n: Int ) : HashSet[FOLTerm] =
    if ( n == 0 )
      new HashSet[FOLTerm]()
    else
      apply( n - 1 ) + SuccTerm( n - 1 )

}

// Constructs the FOLTerm s^k(0)

object SuccTerm
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
