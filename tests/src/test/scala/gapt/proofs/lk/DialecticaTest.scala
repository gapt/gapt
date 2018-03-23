package gapt.proofs.lk

import gapt.examples.{ LinearCutExampleProof, LinearExampleProof }
import gapt.expr._
import gapt.expr.hol.containsHOQuantifier
import gapt.proofs.lkt.normalizeLKt
import gapt.proofs.{ Ant, Suc }
import gapt.proofs.resolution.ResolutionToLKProof
import gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class DialecticaTest extends Specification {

  "1" in {
    val Right( p ) = solvePropositional( hos":- a | ~a" )
    val res = dialectica( p )
    println( res )
    ok
  }
  "2" in {
    val Right( p ) = solvePropositional( hos":- ~ ~a | ~a" )
    val res = dialectica( p )
    println( res )
    ok
  }
  "3" in {
    val p = ResolutionToLKProof( Escargot.getResolutionProof( hos":- ~ ~a | ~a" ).get )
    val res = dialectica( p )
    println( res )
    ok
  }
  "4" in {
    val p = ProofBuilder.
      c( LogicalAxiom( hof"a" ) ).
      u( NegRightRule( _, Ant( 0 ) ) ).
      c( LogicalAxiom( hof"a" ) ).
      u( NegLeftRule( _, Suc( 0 ) ) ).
      u( NegRightRule( _, Ant( 0 ) ) ).
      b( CutRule( _, _, hof"a" ) ).
      u( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) ).
      qed
    println( p )
    val res = dialectica( p )
    println( res )
    ok
  }
  "5a" in {
    val Some( p ) = Escargot.getLKProof( hos"P(0), !x (-P(x) | P(s(x))) :- P(s(s(s(0))))" )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "5" in {
    val p = LinearExampleProof( 2 )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "6" in {
    val p = gapt.examples.fol1.proof
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "7" in {
    import gapt.examples.tape._
    val p = eliminateDefinitions( proof )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "7b" in {
    import gapt.examples.lattice._
    val p = eliminateDefinitions( proof )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "8" in {
    import gapt.examples.Pi3Pigeonhole._
    val p = proof
    val res = dialectica( p )
    println( res._1 )
    println( res._2.map( _.map( BetaReduction.betaNormalize ) ) )
    ok
  }
  "9" in {
    val p = LinearCutExampleProof( 3 )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "10" in {
    val Some( p ) = Escargot.getLKProof( hos"P(0), -P(s(s(0))) :- ?x (P(x) & -P(s(x)))" )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "11" in {
    val Some( p ) = Escargot.withDeskolemization.getLKProof( hos"?x P(f(x)) :- ?x P(x)" )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "12" in {
    val Right( p ) = solvePropositional( hof"a & b -> b & a" )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "13" in {
    val Right( p ) = solvePropositional( hof"(!x p x) & (!x q x) -> (!x q x) & (!x p x)" ).map( AtomicExpansion( _ ) )
    val res = dialectica( p )
    println( res._1 )
    println( res._2 )
    ok
  }
  "14" in {
    import gapt.examples.fol1._
    val p = proof
    val res = dialectica( p )
    println( res._1 )
    println( res._2.map( _.map( BetaReduction.betaNormalize ) ) )
    ok
  }

}
