/**
 * Description:
 */
package gapt.integration_tests

import gapt.examples.lattice
import gapt.expr.formula.hol.isAtom
import gapt.proofs.{ HOLClause, SequentMatchers }
import gapt.proofs.ceres._
import gapt.proofs.lk._
import gapt.provers.escargot.Escargot
import gapt.provers.prover9._
import java.io.File.separator

import gapt.proofs.lk.rules.CutRule
import org.specs2.mutable._

//NOTE: I removed the proof profile from this test

class LatticeTest extends Specification with SequentMatchers {
  "The system" should {
    "parse, skolemize, and extract the clause set for the lattice proof" in {
      val s = extractStruct( lattice.p, CERES.skipEquations )
      val css = CharacteristicClauseSet( s )
      Escargot getResolutionProof css must beSome
    }

    "parse, skolemize and apply CERES to the lattice proof" in {
      val acnf = CERES( lattice.p, CERES.skipNothing, Escargot )
      acnf.endSequent must beMultiSetEqual( lattice.p.endSequent )
      for ( CutRule( p1, a1, p2, a2 ) <- acnf.subProofs ) isAtom( p1.endSequent( a1 ) ) must beTrue
      ok
    }

    "parse, skolemize and apply CERES to the lattice proof, skipping equational inferences" in {
      val acnf = CERES( lattice.p, CERES.skipEquations, Escargot )
      acnf.endSequent must beMultiSetEqual( lattice.p.endSequent )
      for ( CutRule( p1, a1, p2, a2 ) <- acnf.subProofs ) isAtom( p1.endSequent( a1 ) ) must beTrue
      ok
    }

  }
}
