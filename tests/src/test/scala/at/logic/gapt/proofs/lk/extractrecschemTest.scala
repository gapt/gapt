package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.{ Pi2Pigeonhole, tape, tapeUrban }
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.grammars.RecursionScheme
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._
import org.specs2.specification.core.Fragment

class ExtractRecSchemTest extends Specification with SatMatchers {
  "simple" in {
    val p = Lemma(
      ( "base" -> hof"P c" ) +:
        ( "step" -> hof"!x (P x -> P (f x))" ) +:
        Sequent()
        :+ ( "goal" -> hof"P (f (f (f (f c))))" )
    ) {
        cut( "step2", hof"!x (P x -> P (f (f x)))" )
        forget( "goal" ); decompose; escargot
        escargot
      }

    val recSchem = extractRecSchem( p )
    And( recSchem.language ) must beUnsat
  }

  "bottom" in { And( extractRecSchem( BottomAxiom ).language ) must beUnsat }
  "top" in { And( extractRecSchem( TopAxiom ).language ) must beUnsat }

  "pi2 pigeonhole" in {
    val p = Pi2Pigeonhole.proof
    val recSchem = extractRecSchem( p )

    And( recSchem.language ) must beEUnsat
  }

  "tape proof" in {
    import tape._
    val proof = eliminateDefinitions( tape.proof )

    val recSchem = extractRecSchem( proof )
    And( recSchem.language ) must beEUnsat

    val recSchemWithEq = extractRecSchem( proof, includeEqTheory = true )
    And( recSchemWithEq.language ) must beUnsat
  }

  "urban tape proof" in {
    import tapeUrban._
    val proof = eliminateDefinitions( sigma )

    val recSchem = extractRecSchem( proof )
    And( recSchem.language ) must beEUnsat
  }

  "simple pi3" in {
    val p = Lemma(
      ( "hyp" -> hof"∀x ∀y P(x, x, y)" ) +:
        Sequent()
        :+ ( "conj" -> hof"∃x P(c, x, d)" )
    ) {
        cut( "cut", hof"∀x ∃y ∀z P(x, y, z)" )
        forget( "conj" ); decompose; exR( le"x" ).forget; decompose; chain( "hyp" )
        forget( "hyp" ); allL( le"c" ).forget; decompose; exR( le"y" ).forget; chain( "cut" )
      }

    val recschem = extractRecSchem( p )
    And( recschem.language ) must beUnsat
  }

  "numeral induction" in {
    implicit var ctx = Context()
    ctx += Context.InductiveType( "Nat", hoc"Zero: Nat", hoc"Suc: Nat>Nat" )
    ctx += Context.Sort( "Witness" )
    ctx += hoc"p: Nat>Witness>o"
    ctx += hoc"g: Witness>Witness"
    ctx += hoc"c: Witness"

    val proof = Lemma(
      ( "base" -> hof"∀y p(Zero, y)" ) +:
        ( "step" -> hof"∀x ∀y (p(x, g y) ⊃ p(Suc x, y))" ) +:
        Sequent()
        :+ ( "conj" -> hof"p(x, c)" )
    ) {
        cut( "cut", hof"∀x ∀y p(x, y)" ); forget( "conj" )
        allR; induction( hov"x:Nat" ).onAll( decompose )
        chain( "base" )
        chain( "step" ); chain( "IHx_0" )

        chain( "cut" )
      }

    val recSchem = extractRecSchem( proof )
    And( recSchem.parametricLanguage( le"Suc (Suc Zero)" ) ) must beUnsat
  }
}

class Pi2FactorialPOC extends Specification with SatMatchers {
  implicit var ctx = Context()
  ctx += Context.InductiveType( "i", hoc"0:i", hoc"s:i>i" )

  ctx += hoc"'+': i>i>i"
  ctx += hoc"'*': i>i>i"
  ctx += hoc"f: i>i"
  ctx += hoc"g: i>i>i"

  ctx += hoc"A: i>o"
  ctx += hoc"B: i>i>(i>o)>o"
  ctx += hoc"C: i>o"
  ctx += hoc"D: (i>o)>i>i>i>o"

  val hors = RecursionScheme(
    le"A".asInstanceOf[Const],

    le"A z" -> le"B z (s 0) C",
    le"A z" -> le"(s 0) * z = z",
    le"A z" -> le"f z != g (s 0) z",
    le"B (s x) y X" -> le"B x (y * s x) (D X x y)",
    le"D X x y w" -> le"(y * s x) * w = y * (s x * w)",
    le"D X x y w" -> le"g y (s x) = g (y * s x) x",
    le"D X x y w" -> le"f (s x) = s x * f x",
    le"D X x y w" -> le"X (s x * w): o",
    le"B 0 y X" -> le"g y 0 = y",
    le"B 0 y X" -> le"f 0 = s 0",
    le"B 0 y X" -> le"s 0 * s 0 = s 0",
    le"B 0 y X" -> le"X (s 0): o"
  )

  def lang( i: Int ) = hors.parametricLanguage( Numeral( i ) ).map( _.asInstanceOf[Formula] )

  // println( hors )
  // println()
  // lang( 3 ).toSeq.sortBy( _.toString ) foreach println
  // println()

  "termination" in {
    lang( 10 )
    ok
  }

  "languages should be tautologies" in {
    Fragment.foreach( 0 to 7 ) { i =>
      s"n = $i" in {
        And( lang( i ) ) must beEUnsat
      }
    }
  }
}