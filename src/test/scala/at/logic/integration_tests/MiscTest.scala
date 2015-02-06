
package at.logic.integration_tests

import at.logic.algorithms.cutIntroduction._
import at.logic.algorithms.hlk.HybridLatexParser
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.resolution._
import at.logic.algorithms.rewriting.DefinitionElimination
import at.logic.proofs.expansionTrees.{toDeep => ETtoDeep,toShallow => ETtoShallow}
import at.logic.proofs.lk._
import at.logic.proofs.lk.base._
import at.logic.proofs.occurrences._
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.{And => AndHOL, Imp => ImpHOL, Or => OrHOL}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.parsing.calculus.xml.saveXML
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.parsing.veriT.VeriTParser
import at.logic.provers.minisat.MiniSATProver
import at.logic.provers.prover9.{Prover9, Prover9Prover}
import at.logic.provers.veriT.VeriTProver
import at.logic.transformations.ReductiveCutElim
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.transformations.ceres.clauseSets.profile._
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.herbrandExtraction.extractExpansionSequent
import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.skolemization.lksk.LKtoLKskc

import java.util.zip.GZIPInputStream
import java.io.File.separator
import java.io.{FileReader, FileInputStream, InputStreamReader}
import at.logic.proofs.occurrences._
import at.logic.utils.testing.ClasspathFileCopier
import org.junit.runner.RunWith
import org.specs2.execute.Success
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class MiscTest extends SpecificationWithJUnit with ClasspathFileCopier {

  // returns LKProof with end-sequent  P(s^k(0)), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
  private def LinearExampleProof( k : Int, n : Int ) : LKProof = {
    val s = "s"
    val c = "0"
    val p = "P"

    val x = FOLVar("x")
    val ass = AllVar( x, Imp( Atom( p, x::Nil ), Atom( p, Function( s, x::Nil )::Nil ) ) )
    if ( k == n ) // leaf proof
    {
      val a = Atom( p,  Utils.numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val p1 = Atom( p, Utils.numeral( k )::Nil )
      val p2 = Atom( p, Utils.numeral( k + 1 )::Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1::Nil, p1::Nil ), LinearExampleProof( k + 1, n ), p1, p2 ), aux, ass, Utils.numeral( k ) ), ass )
    }
  }

  sequential
  "The system" should {
    /*
//    "parse, skolemize, extract clause set for a simple induction proof" in {
//      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("simple_ind.xml"))) with XMLProofDatabaseParser)..getProofDatabase()
//      proofs.size must beEqualTo(1)
//      val proof = proofs.first
//      val proof_sk = LKtoLKskc( proof )
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
      if (!(new MiniSATProver).isInstalled()) skipped("MiniSAT is not installed")
      val p = LinearExampleProof(0, 7)
      CutIntroduction.one_cut_one_quantifier(p, false)
      Success()
    }

    "skolemize a simple proof" in {
      val proofdb = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sk2.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "skolemize a proof with a simple definition" in {
      val proofdb = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sk3.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "skolemize a proof with a complex definition" in {
      val proofdb = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sk4.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      Success()
    }

    "extract projections and clause set from a skolemized proof" in {
      val proofdb = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("test1p.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val projs = Projections( proof )
      val s = at.logic.transformations.ceres.struct.StructCreators.extract( proof )
      val cs = StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent )
      val prf = deleteTautologies(proofProfile(s, proof).map( _.toFSequent ))
      val path = "target" + separator + "test1p-out.xml"
      saveXML( //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2("cs", cs)::Tuple2("prf", prf)::Nil, path )
      Success()
    }

    "introduce a cut and eliminate it via Gentzen in the LinearExampleProof (n = 4)" in {
      if (!(new MiniSATProver).isInstalled()) skipped("MiniSAT is not installed")

      val p = LinearExampleProof( 0, 4 )
      val pi = CutIntroduction.one_cut_one_quantifier(p, false)
      val pe = ReductiveCutElim.eliminateAllByUppermost(pi, steps = false)

      ReductiveCutElim.isCutFree(p)  must beEqualTo( true )
      ReductiveCutElim.isCutFree(pi) must beEqualTo( false )
      ReductiveCutElim.isCutFree(pe) must beEqualTo( true )
    }

    "extract expansion tree from tape proof" in {
      val tokens = HybridLatexParser.parseFile(tempCopyOfClasspathFile("tape3.llk"))
      val db = HybridLatexParser.createLKProof(tokens)
      // I have no idea why, but this makes the code get the correct proof
      val proofs = db.proofs.filter(_._1.toString == "TAPEPROOF")
      val (_,p)::_ = proofs
      val elp = AtomicExpansion(DefinitionElimination(db.Definitions,p))
      val reg = regularize(elp)
      val lksk_proof = LKtoLKskc(reg)
      // TODO
      val et = extractExpansionSequent(reg, false)  // must throwA[IllegalArgumentException] // currently contains problematic definitions
      ok
    }

    "construct proof with expansion sequent extracted from proof 1/2" in {
      val y = FOLVar("y")
      val x = FOLVar("x")
      val Py = Atom("P", y :: Nil)
      val Px = Atom("P", x :: Nil)
      val AllxPx = AllVar(x, Px)

      // test with 1 weak & 1 strong
      val p1 = Axiom(Py :: Nil, Py :: Nil)
      val p2 = ForallLeftRule(p1, Py, AllxPx, y)
      val p3 = ForallRightRule(p2, Py, AllxPx, y)

      val etSeq = extractExpansionSequent(p3, false)

      val proof = solve.expansionProofToLKProof(p3.root.toFSequent, etSeq)
      proof.isDefined must beTrue
    }

    "construct proof with expansion sequent extracted from proof 2/2" in {
      val proof = LinearExampleProof(0, 4)

      val proofPrime = solve.expansionProofToLKProof(proof.root.toFSequent, extractExpansionSequent(proof, false))
      proofPrime.isDefined must beTrue
    }

    "load veriT proofs pi and verify the validity of Deep(pi) using MiniSAT" in {
      val minisat = new MiniSATProver()
      if (!minisat.isInstalled()) skipped("MiniSAT is not installed")

      for (i <- List(0,1,3)) { // Tests 2 and 4 take comparatively long.
        val p = VeriTParser.getExpansionProof(tempCopyOfClasspathFile(s"test${i}.verit")).get
        val seq = ETtoDeep(p)

        minisat.isValid(seq) must beTrue
      }
      ok
    }

    "load Prover9 proof without equality reasoning, extract expansion tree E, verify deep formula of E using minisat" in {
      val minisat = new MiniSATProver()
      if (!minisat.isInstalled()) skipped("MiniSAT is not installed")
      if (!Prover9.isInstalled()) skipped("Prover9 is not installed")

      val testFilePath = tempCopyOfClasspathFile( "PUZ002-1.out" )

      val lkproof1 = Prover9.parse_prover9LK( testFilePath )
      val expseq = extractExpansionSequent( lkproof1, false )
      val deep = ETtoDeep( expseq )

      minisat.isValid( deep ) must beTrue

      // the next line should work but does not (see issue 279)
      // val lkproof2 = solve.expansionProofToLKProof( ETtoShallow( expseq ), expseq )
    }

    "load Prover9 proof with equality reasoning, extract expansion tree E, verify deep formula of E using veriT" in {
      val veriT = new VeriTProver()
      if (!veriT.isInstalled()) skipped("VeriT is not installed")
      if (!Prover9.isInstalled()) skipped("Prover9 is not installed")

      val testFilePath = tempCopyOfClasspathFile( "ALG004-1.out" )

      val lkProof = Prover9.parse_prover9LK( testFilePath )
      val expansionSequent = extractExpansionSequent(lkProof, false)
      val deep = ETtoDeep(expansionSequent)

      veriT.isValid(deep) must beTrue
    }
  }
}
