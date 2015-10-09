package at.logic.gapt.proofs.lkNew

import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.examples.Pi2Pigeonhole
import at.logic.gapt.expr.{ All, FOLVar, FOLAtom }
import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.provers.prover9.Prover9Prover

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
    if ( !new Prover9Prover().isInstalled ) skipped

    LKToLKsk( Pi2Pigeonhole() )
    ok
  }

  "higher order tape proof" in {
    def load( fn: String ): LKProof = {
      val tokens = HybridLatexParser.parse( Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( fn ) ).mkString )
      val pdb = HybridLatexParser.createLKProof( tokens )
      val pLKOld = at.logic.gapt.proofs.lk.AtomicExpansion( DefinitionElimination( pdb.Definitions, at.logic.gapt.proofs.lk.regularize( pdb.proof( "TAPEPROOF" ) ) ) )
      lkOld2New( pLKOld )
    }

    "2 copies tape proof" in {
      val lk = load( "tape3.llk" )
      val lksk = LKToLKsk( lk )
      lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
    }
    "1 copy tape proof" in {
      val lk = load( "tape3ex.llk" )
      val lksk = LKToLKsk( lk )
      lksk.conclusion must_== ( lk.conclusion map { Seq() -> _ } )
    }
  }
}
