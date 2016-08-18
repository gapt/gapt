package at.logic.gapt.proofs.expansion

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.examples.{ LinearExampleProof, Pi2Pigeonhole }
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.llk.LLKProofParser
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent, SequentMatchers }
import at.logic.gapt.proofs.lk.{ DefinitionElimination, LKToExpansionProof }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification
import better.files._

class ExpansionProofTest extends Specification with SatMatchers with SequentMatchers {

  "linear example cut intro" in {
    val Some( p ) = CutIntroduction( LinearExampleProof( 6 ) )
    val e = LKToExpansionProof( p )
    e.deep must beValidSequent
    eliminateCutsET( e ).deep must beValidSequent
  }

  "reject cyclic proofs" in {
    val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
    ExpansionProof( Sequent() :+ ETWeakQuantifier(
      Ex( x, All( y, x === y ) ),
      Map( x -> ETStrongQuantifier( All( y, x === y ), x, ETAtom( x === x, Polarity.InSuccedent ) ) )
    ) ) must throwA[MatchError]
  }

  "substitute proofs" in {
    val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
    val f = FOLFunctionConst( "f", 1 )
    val r = FOLAtomConst( "r", 2 )

    val proof = ExpansionProof( Sequent() :+ ETStrongQuantifier(
      All( x, r( x, y ) ), x, ETAtom( r( x, y ), Polarity.InSuccedent )
    ) )
    proof.deep must_== ( Sequent() :+ r( x, y ) )

    val proof1 = Substitution( x -> y )( proof )
    proof1.deep must_== ( Sequent() :+ r( x, y ) )

    val proof2 = Substitution( y -> f( x ) )( proof )
    val Seq( x0 ) = proof2.eigenVariables.toSeq
    proof2.deep must_== ( Sequent() :+ r( x0, f( x ) ) )
  }

  "pi2 pigeonhole" in {
    val e = LKToExpansionProof( Pi2Pigeonhole.proof )
    Escargot isValid e.deep must_== true
    Escargot isValid eliminateCutsET( e ).deep must_== true
  }

  "tape proof cut elimination" in {
    val pdb = LLKProofParser( ClasspathInputFile( "tape3ex.llk" ) )
    val lk = DefinitionElimination( pdb.Definitions )( pdb proof "TAPEPROOF" )
    val expansion = LKToExpansionProof( lk )
    val cutfree = eliminateCutsET( expansion )
    if ( !VeriT.isInstalled ) skipped
    VeriT isValid expansion.deep must_== true
    VeriT isValid cutfree.deep must_== true
  }

  "weird cuts" in {
    val epwc = ExpansionProofWithCut(
      Seq( ETImp(
        ETStrongQuantifier( hof"∀x P x", hov"x", ETAtom( hoa"P x", Polarity.InSuccedent ) ),
        ETWeakQuantifier( hof"∀x P x", Map( le"f x" -> ETAtom( hoa"P (f x)", Polarity.InAntecedent ) ) )
      ) ),
      ETWeakQuantifier( hof"∀x P x", Map( le"x" -> ETAtom( hoa"P x", Polarity.InAntecedent ) ) ) +:
        Sequent()
        :+ ETWeakQuantifier( hof"∃x P (f x)", Map( le"x" -> ETAtom( hoa"P (f x)", Polarity.InSuccedent ) ) )
    )
    epwc.deep must beValidSequent
    val ep = eliminateCutsET( epwc )
    ep.deep must beValidSequent
  }

}

class ExpansionProofDefinitionEliminationTest extends Specification with SatMatchers {
  "simple unipolar definition" in {
    implicit var ctx = FiniteContext()
    ctx += Context.Sort( "i" )
    ctx += hoc"P: i>o"
    ctx += hoc"f: i>i"
    ctx += hoc"c: i"
    ctx += hof"D x = (P x ∧ P (f x))"

    val d = ETWeakQuantifier(
      hof"∀x (D x <-> P x ∧ P (f x))",
      Map( le"c" ->
        ETAnd(
          ETImp(
            ETAtom( hoa"D c", Polarity.InSuccedent ),
            ETAnd( ETWeakening( hof"P c", Polarity.InAntecedent ), ETAtom( hoa"P (f c)", Polarity.InAntecedent ) )
          ),
          ETWeakening( hof"P c ∧ P (f c) ⊃ D c", Polarity.InAntecedent )
        ) )
    )
    val f = ETWeakQuantifier(
      hof"∃x (P x ∧ P (f x) ⊃ P (f x))",
      Map( le"c" ->
        ETImp(
          ETDefinedAtom( hoa"D c", Polarity.InAntecedent, ctx.definition( "D" ).get ),
          ETAtom( hoa"P (f c)", Polarity.InSuccedent )
        ) )
    )

    val epwd = ExpansionProof( d +: Sequent() :+ f )
    epwd.deep must beValidSequent

    val epwc = eliminateDefsET( epwd, false, Set( hoc"D: i>o" ) )
    epwc.deep must beValidSequent

    val ep = eliminateCutsET( epwc )
    ep.deep must beValidSequent
  }
}
