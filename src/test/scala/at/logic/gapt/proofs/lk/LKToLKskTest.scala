package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.Pi2Pigeonhole
import at.logic.gapt.expr.{ All, FOLVar, FOLAtom }
import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.provers.prover9.Prover9

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

  "pigeonhole" in {
    if ( !Prover9.isInstalled ) skipped

    LKToLKsk( Pi2Pigeonhole() )
    ok
  }

  "lattice proof" in {
    val pdb = XMLProofDatabaseParser( getClass.getClassLoader.getResourceAsStream( "lattice.xml" ) )
    val lk = DefinitionElimination( pdb.Definitions )( regularize( pdb.proofs.head._2 ) )
    val lksk = LKToLKsk( lk )
    lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
  }

  "tape proof" in {
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
      skipped( "definition elimination violates equality rules, see https://github.com/gapt/gapt/issues/452" )
      val lk = load( "tape3.llk" )
      val lksk = LKToLKsk( lk )
      lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
    }
    "1 copy tape proof" in {
      skipped( "definition elimination violates equality rules, see https://github.com/gapt/gapt/issues/452" )
      val lk = load( "tape3ex.llk" )
      val lksk = LKToLKsk( lk )
      lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
    }
  }
}
