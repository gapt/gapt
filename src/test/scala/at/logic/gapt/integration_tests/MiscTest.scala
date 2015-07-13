
package at.logic.gapt.integration_tests

import at.logic.gapt.examples.LinearExampleProof
import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.expr.fol.Utils
import at.logic.gapt.proofs.lk.cutIntroduction._
import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.proofs.expansionTrees.{ addSymmetry, toDeep => ETtoDeep, ExpansionProofToLK }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.expr._
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.formats.prover9.Prover9TermParser
import at.logic.gapt.provers.FailSafeProver
import at.logic.gapt.provers.minisat.MiniSATProver
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver
import at.logic.gapt.proofs.ceres.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.ceres.clauseSets.profile._
import at.logic.gapt.proofs.ceres.projections.Projections
import at.logic.gapt.proofs.ceres.struct.StructCreators

import java.util.zip.GZIPInputStream
import java.io.File.separator
import java.io.{ FileReader, FileInputStream, InputStreamReader }
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.utils.testing.ClasspathFileCopier
import org.specs2.execute.Success
import org.specs2.mutable._

class MiscTest extends Specification with ClasspathFileCopier {

  sequential
  "The system" should {
    /*
//    "parse, skolemize, extract clause set for a simple induction proof" in {
//      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("simple_ind.xml"))) with XMLProofDatabaseParser)..getProofDatabase()
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
      CutIntroduction.one_cut_one_quantifier( p, false )
      Success()
    }

    "skolemize a simple proof" in {
      val proofdb = ( new XMLReader( new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "sk2.xml" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "skolemize a proof with a simple definition" in {
      val proofdb = ( new XMLReader( new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "sk3.xml" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "skolemize a proof with a complex definition" in {
      val proofdb = ( new XMLReader( new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "sk4.xml" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "extract projections and clause set from a skolemized proof" in {
      val proofdb = ( new XMLReader( new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "test1p.xml" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      val projs = Projections( proof )
      val s = StructCreators.extract( proof )
      val cs = StandardClauseSet.transformStructToClauseSet( s ).map( _.toHOLSequent )
      val prf = deleteTautologies( proofProfile( s, proof ).map( _.toHOLSequent ) )
      val path = "target" + separator + "test1p-out.xml"
      saveXML( //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2( "cs", cs ) :: Tuple2( "prf", prf ) :: Nil, path
      )
      Success()
    }

    "introduce a cut and eliminate it via Gentzen in the LinearExampleProof (n = 4)" in {
      val p = LinearExampleProof( 4 )
      val pi = CutIntroduction.one_cut_one_quantifier( p, false )
      val pe = ReductiveCutElim( pi )

      ReductiveCutElim.isCutFree( p ) must beEqualTo( true )
      ReductiveCutElim.isCutFree( pi ) must beEqualTo( false )
      ReductiveCutElim.isCutFree( pe ) must beEqualTo( true )
    }

    "load Prover9 proof without equality reasoning, introduce a cut and eliminate it via Gentzen" in {
      val fsprover = FailSafeProver.getProver()
      if ( !new Prover9Prover().isInstalled ) skipped( "Prover9 is not installed" )

      val testFilePath = tempCopyOfClasspathFile( "SYN726-1.out" )
      val p1 = new Prover9Prover().reconstructLKProofFromFile( testFilePath )
      val p2 = CutIntroduction.one_cut_many_quantifiers( p1, false )
      val p3 = ReductiveCutElim( p2 )

      ReductiveCutElim.isCutFree( p2 ) must beEqualTo( false )
      ReductiveCutElim.isCutFree( p3 ) must beEqualTo( true )
    }

    "extract expansion tree from tape proof" in {
      val tokens = HybridLatexParser.parseFile( tempCopyOfClasspathFile( "tape3.llk" ) )
      val db = HybridLatexParser.createLKProof( tokens )
      // I have no idea why, but this makes the code get the correct proof
      val proofs = db.proofs.filter( _._1.toString == "TAPEPROOF" )
      val ( _, p ) :: _ = proofs
      val elp = AtomicExpansion( DefinitionElimination( db.Definitions, p ) )
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
      val p2 = ForallLeftRule( p1, Py, AllxPx, y )
      val p3 = ForallRightRule( p2, Py, AllxPx, y )

      val etSeq = LKToExpansionProof( p3 )

      val proof = ExpansionProofToLK( etSeq ) // must not throw exception
      ok
    }

    "construct proof with expansion sequent extracted from proof (2/2)" in {
      val proof = LinearExampleProof( 4 )

      val proofPrime = ExpansionProofToLK( LKToExpansionProof( proof ) ) // must not throw exception
      ok
    }

    "load Prover9 proof without equality reasoning and eliminate cuts via Gentzen" in {
      val fsprover = FailSafeProver.getProver()
      if ( !new Prover9Prover().isInstalled ) skipped( "Prover9 is not installed" )

      val testFilePath = tempCopyOfClasspathFile( "PUZ002-1.out" )
      val p = new Prover9Prover().reconstructLKProofFromFile( testFilePath )
      val q = ReductiveCutElim( p )

      ReductiveCutElim.isCutFree( q ) must beEqualTo( true )
    }

    "load veriT proofs pi and verify the validity of Deep(pi) using minisat or sat4j" in {
      val fsprover = FailSafeProver.getProver()
      for ( i <- List( 0, 1 ) ) { // Tests 2 and 4 take comparatively long, test 3 fails with StackOverflow
        val p = VeriTParser.getExpansionProof( tempCopyOfClasspathFile( s"test${i}.verit" ) ).get
        val taut_p = addSymmetry( p )
        val seq = ETtoDeep( taut_p )

        fsprover.isValid( seq ) must beTrue
      }
      ok
    }

    "prove quasi-tautology by veriT and verify validity using minisat or sat4j (1/2)" in {
      val fsprover = FailSafeProver.getProver()
      val veriT = new VeriTProver()
      if ( !veriT.isInstalled ) skipped( "VeriT is not installed" )

      val F = Prover9TermParser.parseFormula( "a=b -> b=a" )
      val E = veriT.getExpansionSequent( HOLSequent( Nil, F :: Nil ) ).get

      val Edeep = ETtoDeep( E )
      fsprover.isValid( Edeep ) must beTrue
    }

    "prove quasi-tautology by veriT and verify validity using minisat or sat4j (2/2)" in {
      val fsprover = FailSafeProver.getProver()
      val veriT = new VeriTProver()
      if ( !veriT.isInstalled ) skipped( "VeriT is not installed" )

      val C = Prover9TermParser.parseFormula( "f(x_0,y_0) = f(y_0,x_0)" )
      val AS = Prover9TermParser.parseFormula( "f(x_0,y_0)=x_0 -> ( f(y_0,x_0)=y_0 -> x_0=y_0 )" )
      val s = HOLSequent( C :: Nil, AS :: Nil )
      val E = veriT.getExpansionSequent( s ).get

      val Edeep = ETtoDeep( E )
      fsprover.isValid( Edeep ) must beTrue
    }

    "load Prover9 proof without equality reasoning, extract expansion sequent E, verify deep formula of E using minisat or sat4j and readback E to LK" in {
      val fsprover = FailSafeProver.getProver()
      if ( !new Prover9Prover().isInstalled ) skipped( "Prover9 is not installed" )

      val testFilePath = tempCopyOfClasspathFile( "PUZ002-1.out" )

      val lkproof = new Prover9Prover().reconstructLKProofFromFile( testFilePath )
      val expseq = LKToExpansionProof( lkproof )
      val deep = ETtoDeep( expseq )

      fsprover.isValid( deep ) must beTrue

      ExpansionProofToLK( expseq ) // must not throw exception
      ok
    }

    "load Prover9 proof with equality reasoning, extract expansion tree E, verify deep formula of E using veriT" in {
      val veriT = new VeriTProver()
      if ( !veriT.isInstalled ) skipped( "VeriT is not installed" )
      if ( !new Prover9Prover().isInstalled ) skipped( "Prover9 is not installed" )

      val testFilePath = tempCopyOfClasspathFile( "ALG004-1.out" )

      val lkProof = new Prover9Prover().reconstructLKProofFromFile( testFilePath )
      val expansionSequent = LKToExpansionProof( lkProof )
      val deep = ETtoDeep( expansionSequent )

      veriT.isValid( deep ) must beTrue
    }

    "load Prover9 proof without equality reasoning, extract expansion tree E, verify deep formula of E using solvePropositional" in {
      if ( !new Prover9Prover().isInstalled ) skipped( "Prover9 is not installed" )

      val testFilePath = tempCopyOfClasspathFile( "PUZ002-1.out" )

      val lkproof1 = new Prover9Prover().reconstructLKProofFromFile( testFilePath )
      val expseq = LKToExpansionProof( lkproof1 )
      val deep = ETtoDeep( expseq )

      solve.solvePropositional( deep ).isDefined must beTrue
    }

    "load Prover9 proof with top and bottom constants, convert it to sequent calculus and extract the deep formula from its expansion sequent" in {
      if ( !new Prover9Prover().isInstalled ) skipped( "Prover9 is not installed" )
      val testFilePath = tempCopyOfClasspathFile( "NUM484+3.out" )
      val lkproof1 = new Prover9Prover().reconstructLKProofFromFile( testFilePath )
      val expseq = LKToExpansionProof( lkproof1 )
      val deep = ETtoDeep( expseq )
      success( "everything worked fine" )
    }
  }
}
