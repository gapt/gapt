package gapt.examples
import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object gapticExamples {

  val decomposeProof = Proof(
    ( "label1" -> hof"!x (p x & q x)" ) +:
      Sequent()
      :+ ( "label2" -> hof"!y (p y -> q y | r y)" ) ) {
      decompose
      allL( fov"y" )
      decompose
      trivial
    }

  val destructProof = Proof(
    ( "label1" -> hof"a & (b & c)" ) +:
      Sequent()
      :+ ( "label2" -> hof"a | (b | c)" ) ) {
      destruct( "label1" )
      destruct( "label2" )
      trivial
    }

  val destructProof2 = Proof(
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

  val chainProof = Proof(
    ( "a" -> hof"q(f(c))" ) +:
      ( "hyp" -> hof"!x (q x -> p (f x))" ) +:
      Sequent()
      :+ ( "target" -> hof"p(f(f(c)))" ) ) {
      chain( "hyp" ).at( "target" )
      trivial
    }

  val chainProof2 = Proof(
    ( "hyp" -> hof"!x p (f x)" ) +:
      Sequent()
      :+ ( "target" -> hof"p(f(f(c)))" ) ) {
      chain( "hyp" )
    }

  val chainProof3 = Proof(
    ( "a" -> hof"r(f(c))" ) +:
      ( "b" -> hof"q(f(c))" ) +:
      ( "hyp" -> hof"!x (r x -> q x -> p (f x))" ) +:
      Sequent()
      :+ ( "target" -> hof"p(f(f(c)))" ) ) {
      chain( "hyp" )
      trivial
      trivial
    }

  val chainProof4 = Proof(
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

  val eqProof = Proof(
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

  val lemma = Proof(
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

  val lemma2 = Proof(
    ( "A" -> hof"A -> B" ) +:
      Sequent()
      :+ ( "S" -> hof"A & B | -A" ) ) {
      repeat( orR orElse negR orElse andR orElse impL orElse trivial )
    }

  val drinker3 = Proof( Sequent()
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

  val lemma3 = Proof(
    ( "F" -> hof"A -> B" ) +:
      Sequent()
      :+ ( "E" -> hof"B" )
      :+ ( "D" -> hof"?y (P y -> !z P z)" ) ) {
      impL
      insert( drinker3 )
      trivial
    }

  val lemma_ = Proof(
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

  val lemma2_ = Proof(
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

  val direct = Proof(
    ( "A" -> hof"A" ) +: ( "B" -> hof"B" ) +: Sequent() :+ ( "B_" -> hof"B" ) ) {
      trivial
    }

  val lemmaProp = Proof(
    ( "a" -> hof"A -> B" ) +: Sequent() :+ ( "s" -> hof"A&B | -A" ) ) {
      impL
      prop
      prop
    }
}