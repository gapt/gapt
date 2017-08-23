package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object gapticExamples {

  val decomposeLemma = Lemma(
    ( "label1" -> hof"!x (p x & q x)" ) +:
      Sequent()
      :+ ( "label2" -> hof"!y (p y -> q y | r y)" ) ) {
      decompose
      allL( fov"y" )
      decompose
      trivial
    }

  val destructLemma = Lemma(
    ( "label1" -> hof"a & (b & c)" ) +:
      Sequent()
      :+ ( "label2" -> hof"a | (b | c)" ) ) {
      destruct( "label1" )
      destruct( "label2" )
      trivial
    }

  val destructLemma2 = Lemma(
    ( "noise1" -> hof"a" ) +:
      Sequent()
      :+ ( "noise2" -> hof"P(y)" )
      :+ ( "label1" -> hof"a | (b | c)" )
      :+ ( "noise3" -> hof"P(z)" )
      :+ ( "label2" -> hof"a & (b & c)" ) ) {
      destruct( "label1" )
      destruct( "label2" )
      trivial
      trivial
    }

  val chainLemma = Lemma(
    ( "a" -> hof"q(f(c))" ) +:
      ( "hyp" -> hof"!x (q x -> p (f x))" ) +:
      Sequent()
      :+ ( "target" -> hof"p(f(f(c)))" ) ) {
      chain( "hyp" ).at( "target" )
      trivial
    }

  val chainLemma2 = Lemma(
    ( "hyp" -> hof"!x p (f x)" ) +:
      Sequent()
      :+ ( "target" -> hof"p(f(f(c)))" ) ) {
      chain( "hyp" )
    }

  val chainLemma3 = Lemma(
    ( "a" -> hof"r(f(c))" ) +:
      ( "b" -> hof"q(f(c))" ) +:
      ( "hyp" -> hof"!x (r x -> q x -> p (f x))" ) +:
      Sequent()
      :+ ( "target" -> hof"p(f(f(c)))" ) ) {
      chain( "hyp" )
      trivial
      trivial
    }

  val chainLemma4 = Lemma(
    ( "a" -> hof"r(f(c))" ) +:
      ( "b" -> hof"q(f(c))" ) +:
      ( "c" -> hof"w(f(c))" ) +:
      ( "hyp" -> hof"!x (r x & q x & w x -> p (f x))" ) +:
      Sequent()
      :+ ( "target" -> hof"p(f(f(c)))" ) ) {
      chain( "hyp" )
      trivial
      trivial
      trivial
    }

  val eqLemma = Lemma(
    ( "c" -> hof"P(y) & Q(y)" ) +:
      ( "eq1" -> hof"u = v" ) +:
      ( "eq2" -> hof"y = x" ) +:
      ( "a" -> hof"P(u) -> Q(u)" ) +:
      Sequent()
      :+ ( "b" -> hof"P(x) & Q(x)" ) ) {
      eql( "eq1", "a" ) yielding hof"P(v) -> Q(v)"
      eql( "eq1", "a" ) yielding hof"P(v) -> Q(u)"
      eql( "eq2", "b" ).fromRightToLeft
      trivial
    }

  val lemma = Lemma(
    ( "A" -> hof"A -> B" ) +:
      Sequent()
      :+ ( "S" -> hof"A & B | -A" ) ) {
      orR
      negR
      andR
      repeat( trivial )
      impL
      repeat( trivial )
    }

  val lemma2 = Lemma(
    ( "A" -> hof"A -> B" ) +:
      Sequent()
      :+ ( "S" -> hof"A & B | -A" ) ) {
      repeat( orR orElse negR orElse andR orElse impL orElse trivial )
    }

  val drinker3 = Lemma( Sequent()
    :+ ( "E" -> hof"B" )
    :+ ( "E" -> hof"A" )
    :+ ( "D" -> hof"?x (P x -> !y P y)" ) ) {
    exR( le"c" )
    impR
    allR
    exR( le"y" )
    impR
    allR
    trivial
  }

  val lemma3 = Lemma(
    ( "F" -> hof"A -> B" ) +:
      Sequent()
      :+ ( "E" -> hof"B" )
      :+ ( "D" -> hof"?y (P y -> !z P z)" ) ) {
      impL
      insert( drinker3 )
      trivial
    }

  val lemma_ = Lemma(
    ( "initAnt" -> hof"A -> B" ) +:
      Sequent()
      :+ ( "initSuc" -> hof"A & B | -A" ) ) {
      orR( "initSuc" )
      negR( "initSuc_1" )
      andR( "initSuc_0" )
      axiomLog
      impL( "initAnt" )
      axiomLog
      axiomLog
    }

  val lemma2_ = Lemma(
    ( "initAnt" -> hof"A -> B" ) +:
      Sequent()
      :+ ( "initSuc" -> hof"A & B | -A" ) ) {
      orR( "initSuc" )
      negR( "initSuc_1" )
      andR( "initSuc_0" )
      trivial
      impL
      trivial
      trivial
    }

  val direct = Lemma(
    ( "A" -> hof"A" ) +: ( "B" -> hof"B" ) +: Sequent() :+ ( "B_" -> hof"B" ) ) {
      trivial
    }

  val lemmaProp = Lemma(
    ( "a" -> hof"A -> B" ) +: Sequent() :+ ( "s" -> hof"A&B | -A" ) ) {
      impL
      prop
      prop
    }
}