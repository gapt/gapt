package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.Pi2Pigeonhole
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.SkolemSymbolFactory
import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.formats.llkNew.exportLLK
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.proofs.{ Suc, Ant }
import at.logic.gapt.proofs.lkOld
import at.logic.gapt.formats.llk

import org.specs2.mutable._

import scala.io.Source

class LKToLKskTest extends Specification {
  "single strong quantifier inference" in {
    val f = FOLAtom( "p", FOLVar( "x" ) )
    val qf = All( FOLVar( "x" ), f )

    val p1 = LogicalAxiom( f )
    val p2 = ForallLeftRule( p1, qf )
    val p3 = ForallRightRule( p2, qf )

    val pSk = LKToLKsk( p3 )
    pSk.conclusion must_== ( p3.endSequent map { Seq() -> _ } )
  }

  "a proof with contractions" in {
    //skipped( "bug: see https://github.com/gapt/gapt/issues/467" )
    /* This proof has 8 skolem constants, since the antecedent occurrence of the formula has 4 different strong
       Ex quantifier occurrences, their instantiation in the succedent creates 4 different paths.
     */

    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p1 = OrLeftRule( p0, Ant( 0 ), p0, Ant( 0 ) )
    val p2 = ContractionRightRule( p1, Suc( 0 ), Suc( 1 ) )
    val p3 = OrLeftRule( p2, Ant( 0 ), p2, Ant( 0 ) )
    //println( exportLLK( p3 ) )

    //println( llk.exportLLK( lkOld.LKToLKsk( lkNew2Old( p3 ) ) ) )

    val factory = new SkolemSymbolFactory

    val lksk = new LKToLKsk( factory )( p3 )

    val sym = factory.getSkolemSymbol
    sym.s must_== "s_{8}"
  }

  "a proof with contractions and cut (1)" in {
    //skipped( "bug: see https://github.com/gapt/gapt/issues/467" )
    /* This proof has 2 skolem constants, since the pseudo cut on P allows us to contract both sides. Then we need to
       share both skolem constants in the two parent branches p1 and p2.
     */
    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val p = HOLAtom( Const( "P", To ), Nil )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p1 = WeakeningRightRule( p0, p )
    val p2 = WeakeningLeftRule( p0, p )
    val p3 = CutRule( p1, p2, p )
    val p4 = ContractionLeftRule( p3, Ant( 0 ), Ant( 1 ) )
    val p5 = ContractionRightRule( p4, Suc( 0 ), Suc( 1 ) )

    val factory = new SkolemSymbolFactory
    val lksk = new LKToLKsk( factory )( p5 )
    val sym = factory.getSkolemSymbol
    sym.s must_== "s_{2}"
  }

  "a proof with contractions and cut (2)" in {
    //skipped( "bug: see https://github.com/gapt/gapt/issues/467" )
    /* This proof has 3 skolem constants. Since we skip the contraction on the right hand side, we share the skolem
       constant for the All quantifier, but not for the Ex quantifier.
     */
    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val p = HOLAtom( Const( "P", To ), Nil )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p0a = AtomicExpansion( f )
    val p1 = WeakeningRightRule( p0, p )
    val p2 = WeakeningLeftRule( p0a, p )
    val p3 = CutRule( p1, p2, p )
    val p4 = ContractionLeftRule( p3, Ant( 0 ), Ant( 1 ) )

    val factory = new SkolemSymbolFactory
    val lksk = new LKToLKsk( factory )( p4 )
    val sym = factory.getSkolemSymbol
    sym.s must_== "s_{3}"
  }

  "a proof with contractions and cut (3)" in {
    //skipped( "bug: see https://github.com/gapt/gapt/issues/467" )
    /* This proof has 4 skolem constants. Since we skip the contraction on the left hand side, we have different
       skolem constants for the All quantifiers. Similar to the non-cut version, this breaks the homomorphy property and
       we also need to create fresh constants for the Ex quantifiers.
     */
    val x = Var( "X", Ti -> To )
    val y = Var( "y", Ti )
    val p = HOLAtom( Const( "P", To ), Nil )
    val f = Ex( y, All( x, App( x, y ) ) )
    val p0 = AtomicExpansion( f )
    val p0a = AtomicExpansion( f )
    val p1 = WeakeningRightRule( p0, p )
    val p2 = WeakeningLeftRule( p0a, p )
    val p3 = CutRule( p1, p2, p )
    val p4 = ContractionRightRule( p3, Suc( 0 ), Suc( 1 ) )

    val factory = new SkolemSymbolFactory
    val lksk = new LKToLKsk( factory )( p4 )
    val sym = factory.getSkolemSymbol
    sym.s must_== "s_{4}"
  }

  "pigeonhole" in {
    LKToLKsk( Pi2Pigeonhole() )
    ok
  }

  "lattice proof" in {
    //skipped( "save time" )
    val pdb = XMLProofDatabaseParser( getClass.getClassLoader.getResourceAsStream( "lattice.xml" ) )
    val lk = DefinitionElimination( pdb.Definitions )( regularize( pdb.proofs.head._2 ) )
    val lksk = LKToLKsk( lk )
    lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
  }

  "tape proof" in {
    //skipped( "save time" )
    val pdb = XMLProofDatabaseParser( getClass.getClassLoader getResourceAsStream "tape-in.xml.gz", enable_compression = true )
    val lk = DefinitionElimination( pdb.Definitions )( regularize( pdb proof "the-proof" ) )
    val lksk = LKToLKsk( lk )
    lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
  }

  "higher order tape proof" in {
    def load( fn: String ): LKProof = {
      val tokens = HybridLatexParser.parse( Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString )
      val pdb = HybridLatexParser.createLKProof( tokens )
      AtomicExpansion( DefinitionElimination( pdb.Definitions )( pdb proof "TAPEPROOF" ) )
    }

    "2 copies tape proof" in {
      //skipped( "save time" )
      val lk = load( "tape3.llk" )
      val lksk = LKToLKsk( lk )
      lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
    }
    "1 copy tape proof" in {
      //skipped( "save time" )
      val lk = load( "tape3ex.llk" )
      val lksk = LKToLKsk( lk )
      lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
    }
  }
}
