package at.logic.gapt.proofs.expansion

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.examples.{ Pi2Pigeonhole, LinearExampleProof }
import at.logic.gapt.expr._
import at.logic.gapt.formats.llkNew.LLKProofParser
import at.logic.gapt.proofs.{ SequentMatchers, Sequent }
import at.logic.gapt.proofs.lk.{ DefinitionElimination, LKToExpansionProof }
import at.logic.gapt.proofs.lkOld.base.beSyntacticMultisetEqual
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.veriT.VeriT
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

import scala.io.Source

class ExpansionProofTest extends Specification with SatMatchers with SequentMatchers {

  "linear example cut intro" in {
    val Some( p ) = CutIntroduction.compressLKProof( LinearExampleProof( 6 ) )
    val e = LKToExpansionProof( p )
    e.deep must beValidSequent
    eliminateCutsET( e ).deep must beValidSequent
  }

  "reject cyclic proofs" in {
    val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
    ExpansionProof( Sequent() :+ ETWeakQuantifier(
      Ex( x, All( y, x === y ) ),
      Map( x -> ETStrongQuantifier( All( y, x === y ), x, ETAtom( x === x, true ) ) )
    ) ) must throwA[MatchError]
  }

  "substitute proofs" in {
    val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
    val f = FOLFunctionConst( "f", 1 )
    val r = FOLAtomConst( "r", 2 )

    val proof = ExpansionProof( Sequent() :+ ETStrongQuantifier(
      All( x, r( x, y ) ), x, ETAtom( r( x, y ), true )
    ) )
    proof.deep must_== ( Sequent() :+ r( x, y ) )

    val proof1 = Substitution( x -> y )( proof )
    proof1.deep must_== ( Sequent() :+ r( x, y ) )

    val proof2 = Substitution( y -> f( x ) )( proof )
    val Seq( x0 ) = proof2.eigenVariables.toSeq
    proof2.deep must_== ( Sequent() :+ r( x0, f( x ) ) )
  }

  "pi2 pigeonhole" in {
    val e = LKToExpansionProof( Pi2Pigeonhole() )
    Escargot isValid e.deep must_== true
    Escargot isValid eliminateCutsET( e ).deep must_== true
  }

  "tape proof cut elimination" in {
    val pdb = LLKProofParser.parseString( Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( "tape3ex.llk" ) ).mkString )
    val lk = DefinitionElimination( pdb.Definitions )( pdb proof "TAPEPROOF" )
    val expansion = LKToExpansionProof( lk )
    Escargot isValid expansion.deep must_== true
    val cutfree = eliminateCutsET( expansion )
    if ( !VeriT.isInstalled ) skipped
    VeriT isValid cutfree.deep must_== true
  }

}
