package at.logic.gapt.proofsNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, SequentMatchers, Suc }
import at.logic.gapt.proofsNew.lk.{ ContractionRight, LKProofBuilder, LogicalAxiom, NegRight, OrLeft, OrRight }
import org.specs2.mutable.Specification

class LKNewTest extends Specification with SequentMatchers {

  "example" in {
    val p = LKProofBuilder.
      c( LogicalAxiom( hof"X" ) ).
      u( NegRight( _, Ant( 0 ) ) ).
      u( OrRight( _, Suc( 0 ), Suc( 1 ) ) ).
      qed
    p.conclusion must_== hos":- X | -X"
    Substitution( hov"X:o" -> hof"P" )( p ).conclusion must_== hos":- P | -P"
  }

  "setlike" in {
    val p = LKProofBuilder.
      c( LogicalAxiom( hof"p" ) ).
      c( LogicalAxiom( hof"p" ) ).
      b( OrLeft( _, Ant( 0 ), _, Ant( 0 ) ) ).
      u( ContractionRight( _, Suc( 0 ), Suc( 1 ) ) ).
      qed
    p.conclusion must_== hos"p | p :- p"
    val q = setlikeLK.lkToSetlikeLK( p )
    println( q )
    q.conclusion.sequent must beSetEqual( hos"p | p :- p" )
  }

}
