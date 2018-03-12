package gapt.proofs.expansion

import gapt.cutintro.CutIntroduction
import gapt.examples.{ LinearExampleProof, Pi2Pigeonhole }
import gapt.expr._
import gapt.formats.ClasspathInputFile
import gapt.formats.llk.LLKProofParser
import gapt.proofs.{ Context, Sequent, SequentMatchers }
import gapt.proofs.lk.{ eliminateDefinitions, LKToExpansionProof }
import gapt.provers.escargot.Escargot
import gapt.provers.verit.VeriT
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

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
      Map( x -> ETStrongQuantifier( All( y, x === y ), x, ETAtom( x === x, Polarity.InSuccedent ) ) ) ) ) must throwA[MatchError]
  }

  "substitute proofs" in {
    val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
    val f = FOLFunctionConst( "f", 1 )
    val r = FOLAtomConst( "r", 2 )

    val proof = ExpansionProof( Sequent() :+ ETStrongQuantifier(
      All( x, r( x, y ) ), x, ETAtom( r( x, y ), Polarity.InSuccedent ) ) )
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
    val lk = eliminateDefinitions( pdb.Definitions )( pdb proof "TAPEPROOF" )
    val expansion = LKToExpansionProof( lk )
    val cutfree = eliminateCutsET( expansion )
    if ( !VeriT.isInstalled ) skipped
    VeriT isValid expansion.deep must_== true
    VeriT isValid cutfree.deep must_== true
  }

  "weird cuts" in {
    val epwc = ExpansionProof(
      Seq( ETImp(
        ETStrongQuantifier( hof"∀x P x", hov"x", ETAtom( hoa"P x", Polarity.InSuccedent ) ),
        ETWeakQuantifier( hof"∀x P x", Map( le"f x" -> ETAtom( hoa"P (f x)", Polarity.InAntecedent ) ) ) ) ) ++:
        ETWeakQuantifier( hof"∀x P x", Map( le"x" -> ETAtom( hoa"P x", Polarity.InAntecedent ) ) ) +:
        Sequent()
        :+ ETWeakQuantifier( hof"∃x P (f x)", Map( le"x" -> ETAtom( hoa"P (f x)", Polarity.InSuccedent ) ) ) )
    epwc.deep must beValidSequent
    val ep = eliminateCutsET( epwc )
    ep.deep must beValidSequent
  }

  "merge skolem and strong quantifiers" in {
    val ep = ExpansionProof(
      ETWeakQuantifier( hof"∀x P x", Map(
        le"y" -> ETAtom( hoa"P y", Polarity.InAntecedent ),
        le"sk" -> ETAtom( hoa"P sk", Polarity.InAntecedent ) ) ) +: Sequent()
        :+ ETMerge(
          ETStrongQuantifier( hof"∀x P x", hov"y", ETAtom( hoa"P y", Polarity.InSuccedent ) ),
          ETSkolemQuantifier( hof"∀x P x", le"sk", le"∀x P x", ETAtom( hoa"P sk", Polarity.InSuccedent ) ) ) )
    ep.deep must beValidSequent
    val merged = eliminateMerges( ep )
    merged.deep must beValidSequent
    merged must beLike { case e if !e.subProofs.exists( _.isInstanceOf[ETMerge] ) => ok }
  }

}

class ExpansionProofDefinitionEliminationTest extends Specification with SatMatchers {
  "simple unipolar definition" in {
    implicit var ctx = Context()
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
            ETAnd( ETWeakening( hof"P c", Polarity.InAntecedent ), ETAtom( hoa"P (f c)", Polarity.InAntecedent ) ) ),
          ETWeakening( hof"P c ∧ P (f c) → D c", Polarity.InAntecedent ) ) ) )
    val f = ETWeakQuantifier(
      hof"∃x (P x ∧ P (f x) → P (f x))",
      Map( le"c" ->
        ETImp(
          ETDefinition( hof"P c & P (f c)", ETAtom( hoa"D c", Polarity.InAntecedent ) ),
          ETAtom( hoa"P (f c)", Polarity.InSuccedent ) ) ) )

    val epwd = ExpansionProof( d +: Sequent() :+ f )
    epwd.deep must beValidSequent

    val epwc = eliminateDefsET( epwd, false, Set( hoc"D: i>o" ) )
    epwc.deep must beValidSequent

    val ep = eliminateCutsET( epwc )
    ep.deep must beValidSequent
  }
}
