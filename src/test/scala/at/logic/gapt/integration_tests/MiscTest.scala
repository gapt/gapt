
package at.logic.gapt.integration_tests

import java.io.InputStreamReader

import at.logic.gapt.examples.LinearExampleProof
import at.logic.gapt.formats.llkNew.LLKProofParser
import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.cutintro._
import at.logic.gapt.proofs.expansion.{ toDeep => ETtoDeep, eliminateCutsET, addSymmetry, ExpansionProofToLK }
import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.formats.prover9.Prover9TermParser
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.prover9.{ Prover9Importer, Prover9 }
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.veriT.VeriT
import at.logic.gapt.proofs.ceres._
import java.io.File.separator
import org.specs2.execute.Success
import org.specs2.mutable._

import scala.io.Source

class MiscTest extends Specification {

  "The system" should {
    /*
//    "parse, skolemize, extract clause set for a simple induction proof" in {
//      val proofs = (new XMLReader((getClass.getClassLoader.getResourceAsStream("simple_ind.xml"))) with XMLProofDatabaseParser)..getProofDatabase()
//      proofs.size must beEqualTo(1)
//      val proof = proofs.first
//      val proof_sk = LKToLKsk( proof )
//      val s = StructCreators.extract( proof_sk )
//      val cs = StandardClauseSet.transformStructToClauseSet( s )
//      val dcs = deleteTautologies( cs )
//      val css = setNormalize( dcs )
//      val cs_path = "target" + separator + "simple_ind-cs.xml"
//      saveXML( Tuple2("cs", cs)::Tuple2("dcs", dcs)::Tuple2("css", (css.toList))::Nil, cs_path )
//      (new java.io.File( cs_path ) ).exists() must beEqualTo( true )
//    }
//    */

    "perform cut introduction on an example proof" in {
      val p = LinearExampleProof( 7 )
      CutIntroduction.compressLKProof( p, method = DeltaTableMethod( manyQuantifiers = false ), verbose = false ) must beSome
    }

    "skolemize a simple proof" in {
      val proofdb = ( new XMLReader( getClass.getClassLoader.getResourceAsStream( "sk2.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "skolemize a proof with a simple definition" in {
      val proofdb = ( new XMLReader( getClass.getClassLoader.getResourceAsStream( "sk3.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "skolemize a proof with a complex definition" in {
      val proofdb = ( new XMLReader( getClass.getClassLoader.getResourceAsStream( "sk4.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "extract projections and clause set from a skolemized proof" in {
      val proofdb = ( new XMLReader( getClass.getClassLoader.getResourceAsStream( "test1p.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val projs = Projections( proof )
      val s = StructCreators.extract( proof )
      val cs = CharacteristicClauseSet( s )
      val path = "target" + separator + "test1p-out.xml"
      val oldproofs_with_names = projs.toList.zipWithIndex.map( p => ( "\\psi_{" + p._2 + "}", lkNew2Old( p._1 ) ) )
      saveXML(
        oldproofs_with_names,
        ( "cs", cs.toList ) :: Nil, path
      )
      Success()
    }

    "introduce a cut and eliminate it via Gentzen in the LinearExampleProof (n = 4)" in {
      val p = LinearExampleProof( 4 )
      val Some( pi ) = CutIntroduction.compressLKProof( p, method = DeltaTableMethod( manyQuantifiers = false ), verbose = false )
      val pe = ReductiveCutElimination( pi )

      ReductiveCutElimination.isCutFree( p ) must beEqualTo( true )
      ReductiveCutElimination.isCutFree( pi ) must beEqualTo( false )
      ReductiveCutElimination.isCutFree( pe ) must beEqualTo( true )
    }

    "load Prover9 proof without equality reasoning, introduce a cut and eliminate it via Gentzen" in {
      if ( !Prover9.isInstalled ) skipped( "Prover9 is not installed" )

      val p1 = lkProofFromClasspath( "SYN726-1.out" )
      val Some( p2 ) = CutIntroduction.compressLKProof( p1, method = DeltaTableMethod( manyQuantifiers = true ), verbose = false )
      val p3 = ReductiveCutElimination( p2 )

      ReductiveCutElimination.isCutFree( p2 ) must beEqualTo( false )
      ReductiveCutElimination.isCutFree( p3 ) must beEqualTo( true )
    }

    "extract expansion tree from tape proof" in {
      val db = LLKProofParser.parseString( Source.fromInputStream( getClass.getClassLoader getResourceAsStream "tape3.llk" ).mkString )
      // I have no idea why, but this makes the code get the correct proof
      val p = db.proof( "TAPEPROOF" )
      val elp = AtomicExpansion( DefinitionElimination( db.Definitions )( p ) )
      val reg = regularize( elp )
      val lksk_proof = LKToLKsk( reg )
      // TODO
      val et = LKToExpansionProof( reg ) // must throwA[IllegalArgumentException] // currently contains problematic definitions
      ok
    }

    "construct proof with expansion sequent extracted from proof (1/2)" in {
      val y = FOLVar( "y" )
      val x = FOLVar( "x" )
      val Py = FOLAtom( "P", y :: Nil )
      val Px = FOLAtom( "P", x :: Nil )
      val AllxPx = All( x, Px )

      // test with 1 weak & 1 strong
      val p1 = Axiom( Py :: Nil, Py :: Nil )
      val p2 = ForallLeftRule( p1, AllxPx, y )
      val p3 = ForallRightRule( p2, AllxPx, y )

      val etSeq = eliminateCutsET( LKToExpansionProof( p3 ) )

      val proof = ExpansionProofToLK( etSeq ) // must not throw exception
      ok
    }

    "construct proof with expansion sequent extracted from proof (2/2)" in {
      val proof = LinearExampleProof( 4 )

      val proofPrime = ExpansionProofToLK( eliminateCutsET( LKToExpansionProof( proof ) ) ) // must not throw exception
      ok
    }

    "load Prover9 proof without equality reasoning and eliminate cuts via Gentzen" in {
      if ( !Prover9.isInstalled ) skipped( "Prover9 is not installed" )

      val p = lkProofFromClasspath( "PUZ002-1.out" )
      val q = ReductiveCutElimination( p )

      ReductiveCutElimination.isCutFree( q ) must beEqualTo( true )
    }

    "load veriT proofs pi and verify the validity of Deep(pi) using sat4j" in {
      for ( i <- List( 0, 1 ) ) { // Tests 2 and 4 take comparatively long, test 3 fails with StackOverflow
        val p = VeriTParser.getExpansionProof( new InputStreamReader( getClass.getClassLoader getResourceAsStream s"test${i}.verit" ) ).get
        val taut_p = addSymmetry( p )
        val seq = ETtoDeep( taut_p )

        Sat4j.isValid( seq ) must beTrue
      }
      ok
    }

    "prove quasi-tautology by veriT and verify validity using sat4j (1/2)" in {
      if ( !VeriT.isInstalled ) skipped( "VeriT is not installed" )

      val F = Prover9TermParser.parseFormula( "a=b -> b=a" )
      val E = VeriT.getExpansionProof( HOLSequent( Nil, F :: Nil ) ).get

      val Edeep = ETtoDeep( E )
      Sat4j.isValid( Edeep ) must beTrue
    }

    "prove quasi-tautology by veriT and verify validity using sat4j (2/2)" in {
      if ( !VeriT.isInstalled ) skipped( "VeriT is not installed" )

      val C = Prover9TermParser.parseFormula( "f(x_0,y_0) = f(y_0,x_0)" )
      val AS = Prover9TermParser.parseFormula( "f(x_0,y_0)=x_0 -> ( f(y_0,x_0)=y_0 -> x_0=y_0 )" )
      val s = HOLSequent( C :: Nil, AS :: Nil )
      val E = VeriT.getExpansionProof( s ).get

      val Edeep = ETtoDeep( E )
      Sat4j.isValid( Edeep ) must beTrue
    }

    def lkProofFromClasspath( filename: String ) =
      Prover9Importer lkProof Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( filename ) ).mkString

    "load Prover9 proof without equality reasoning, extract expansion sequent E, verify deep formula of E using sat4j and readback E to LK" in {
      if ( !Prover9.isInstalled ) skipped( "Prover9 is not installed" )

      val lkproof = lkProofFromClasspath( "PUZ002-1.out" )
      val expseq = LKToExpansionProof( lkproof )
      val deep = ETtoDeep( expseq )

      Sat4j.isValid( deep ) must beTrue

      ExpansionProofToLK( eliminateCutsET( expseq ) ) // must not throw exception
      ok
    }

    "load Prover9 proof with equality reasoning, extract expansion tree E, verify deep formula of E using veriT" in {
      if ( !VeriT.isInstalled ) skipped( "VeriT is not installed" )
      if ( !Prover9.isInstalled ) skipped( "Prover9 is not installed" )

      val lkProof = lkProofFromClasspath( "ALG004-1.out" )
      val expansionSequent = LKToExpansionProof( lkProof )
      val deep = ETtoDeep( expansionSequent )

      VeriT.isValid( deep ) must beTrue
    }

    "load Prover9 proof without equality reasoning, extract expansion tree E, verify deep formula of E using solvePropositional" in {
      if ( !Prover9.isInstalled ) skipped( "Prover9 is not installed" )

      val lkproof1 = lkProofFromClasspath( "PUZ002-1.out" )
      val expseq = LKToExpansionProof( lkproof1 )
      val deep = ETtoDeep( expseq )

      solve.solvePropositional( deep ).isDefined must beTrue
    }

    "load Prover9 proof with top and bottom constants, convert it to sequent calculus and extract the deep formula from its expansion sequent" in {
      if ( !Prover9.isInstalled ) skipped( "Prover9 is not installed" )
      val lkproof1 = lkProofFromClasspath( "NUM484+3.out" )
      val expseq = LKToExpansionProof( lkproof1 )
      val deep = ETtoDeep( expseq )
      success( "everything worked fine" )
    }
  }
}
