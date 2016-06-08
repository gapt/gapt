/**
 * Description:
 */
package at.logic.gapt.integration_tests

import at.logic.gapt.examples.lattice
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.proofs.{ SequentMatchers, HOLClause }
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9._
import java.io.File.separator
import org.specs2.mutable._

//NOTE: I removed the proof profile from this test

class LatticeTest extends Specification with SequentMatchers {
  "The system" should {
    "parse, skolemize, and extract the clause set for the lattice proof" in {
      val proof = skolemize( DefinitionElimination( lattice.defs )( lattice.p ) )

      val s = extractStruct( proof, CERES.skipEquations )
      val css = CharacteristicClauseSet( s )
      Escargot getResolutionProof css must beSome
    }

    "parse, skolemize and apply CERES to the lattice proof" in {
      val proof = skolemize( DefinitionElimination( lattice.defs )( lattice.p ) )

      val acnf = CERES( skolemize( proof ), CERES.skipNothing, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
      for ( CutRule( p1, a1, p2, a2 ) <- acnf.subProofs ) isAtom( p1.endSequent( a1 ) ) must beTrue
      ok
    }

    "parse, skolemize and apply CERES to the lattice proof, skipping equational inferences" in {
      val proof = skolemize( DefinitionElimination( lattice.defs )( lattice.p ) )

      val acnf = CERES( skolemize( proof ), CERES.skipEquations, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
      for ( CutRule( p1, a1, p2, a2 ) <- acnf.subProofs ) isAtom( p1.endSequent( a1 ) ) must beTrue
      ok
    }

  }
}
