package at.logic.gapt.provers.inductionProver
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ Utils, FOLSubstitution }
import at.logic.gapt.proofs.expansionTrees.{ formulaToExpansionTree, ExpansionSequent }
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.provers.prover9.{ Prover9, Prover9Prover }
import at.logic.gapt.provers.sat4j.Sat4jProver
import org.specs2.mutable._
import org.specs2.specification.core.Fragment

class CanonicalSolutionTest extends Specification {
  import SimpleInductionProof._

  val x = FOLVar( "x" )
  val f0 = FOLAtom( "P", FOLConst( "0" ) )
  val f1 = All( x, Imp( FOLAtom( "P", x ), FOLAtom( "P", FOLFunction( "s", x ) ) ) )
  val f2 = FOLAtom( "P", alpha )

  val seq0 = ExpansionSequent( Seq(), Seq() )
  val seq1 = ExpansionSequent(
    Seq( formulaToExpansionTree( f1, List( FOLSubstitution( x -> nu ) ), false ) ),
    Seq() )
  val seq2 = ExpansionSequent(
    Seq( formulaToExpansionTree( f0, false ) ),
    Seq( formulaToExpansionTree( f2, true ) ) )

  val ts = List( FOLConst( "0" ) )
  val us = List( FOLConst( "0" ) )

  val sip = new SimpleInductionProof( seq0, seq1, seq2, ts, us )

  val sol = Imp( FOLAtom( "P", FOLConst( "0" ) ), FOLAtom( "P", nu ) )

  Fragment.foreach( 0 until 5 ) { i =>
    s"C_$i" in {
      val C_i = canonicalSolution( sip, i )
      "have induction formula as consequence" in {
        val imp = Imp( C_i, FOLSubstitution( nu -> Utils.numeral( i ) )( sol ) )
        // we don't use equalities in this example, so we can use SAT.
        new Sat4jProver().isValid( imp ) must beTrue
      }
      "be provable from the background theory" in {
        if ( !Prover9.isInstalled ) skipped
        new Prover9Prover().isValid( FSequent( Seq( f0, f1 ), Seq( C_i ) ) ) must beTrue
      }
    }
  }

}
