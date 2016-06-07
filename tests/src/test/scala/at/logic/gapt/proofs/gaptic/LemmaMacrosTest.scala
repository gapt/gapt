package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import org.specs2.mutable.Specification

class LemmaMacrosTest extends Specification {

  "lemma" in {
    Lemma( Sequent() :+ ( "goal" -> hof"a -> a" ) ) {
      decompose
      trivial
    }
    ok
  }

  "incomplete" in {
    IncompleteLemma( Sequent() :+ ( "goal" -> hof"(a -> a) & b" ) ) {
      destruct( "goal" )
      decompose; trivial
    }
    ok
  }

}
