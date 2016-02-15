package at.logic.gapt.examples

import at.logic.gapt.expr.FOLVar
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object complex {
  val decomposeLemma = Lemma(
    Sequent( Seq( "label1" -> parseFormula( "(all x (p(x) & q(x)))" ) ), Seq( "label2" -> parseFormula( "(all y (p(y) -> (q(y) | r(y))))" ) ) )
  ) {
      decompose
      allL( FOLVar( "y" ) )
      decompose
      axiom
    }

  val destructLemma = Lemma(
    Sequent( Seq( "label1" -> parseFormula( "a & (b & c)" ) ), Seq( "label2" -> parseFormula( "a | (b | c)" ) ) )
  ) {
      destruct( "label1" )
      destruct( "label2" )
      axiom
    }

  val destructLemma2 = Lemma(
    Sequent( Seq( "noise1" -> parseFormula( "a" ) ), Seq( "noise2" -> parseFormula( "P(y)" ), "label1" -> parseFormula( "a | (b | c)" ), "noise3" -> parseFormula( "P(z)" ), "label2" -> parseFormula( "a & (b & c)" ) ) )
  ) {
      destruct( "label1" )
      destruct( "label2" )
      axiom
      axiom
    }

  val chainLemma = Lemma(
    Sequent( Seq( "a" -> parseFormula( "q(f(c))" ), "hyp" -> parseFormula( "(all x (q(x) -> p(f(x))))" ) ), Seq( "target" -> parseFormula( "p(f(f(c)))" ) ) )
  ) {
      chain( "hyp" ).at( "target" )
      axiom
    }

  val chainLemma2 = Lemma(
    Sequent( Seq( "hyp" -> parseFormula( "(all x (p(f(x))))" ) ), Seq( "target" -> parseFormula( "p(f(f(c)))" ) ) )
  ) {
      chain( "hyp" )
    }

  val chainLemma3 = Lemma(
    Sequent( Seq( "a" -> parseFormula( "r(f(c))" ), "b" -> parseFormula( "q(f(c))" ), "hyp" -> parseFormula( "(all x (r(x) -> (q(x) -> p(f(x)))))" ) ), Seq( "target" -> parseFormula( "p(f(f(c)))" ) ) )
  ) {
      chain( "hyp" )
      axiom
      axiom
    }

  val chainLemma4 = Lemma(
    Sequent( Seq( "a" -> parseFormula( "r(f(c))" ), "b" -> parseFormula( "q(f(c))" ), "c" -> parseFormula( "w(f(c))" ), "hyp" -> parseFormula( "(all x ((r(x) & q(x) & w(x)) -> p(f(x))))" ) ), Seq( "target" -> parseFormula( "p(f(f(c)))" ) ) )
  ) {
      chain( "hyp" )
      axiom
      axiom
      axiom
    }
}

