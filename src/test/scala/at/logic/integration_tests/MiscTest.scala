
package at.logic.integration_tests

import at.logic.algorithms.cutIntroduction._
import at.logic.algorithms.hlk.HybridLatexParser
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.resolution._
import at.logic.algorithms.rewriting.DefinitionElimination
import at.logic.calculi.expansionTrees.{toDeep => ETtoDeep,toShallow => ETtoShallow}
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
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
import at.logic.calculi.occurrences._
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
      //println("skolemized proof:")
      //println(proof_sk)
      Success()
    }

    "skolemize a proof with a simple definition" in {
      val proofdb = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sk3.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      //println("skolemized proof:")
      //println(proof_sk)
      Success()
    }

    "skolemize a proof with a complex definition" in {
      val proofdb = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sk4.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      //println("skolemized proof:")
      //println(proof_sk)
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

/*
    //Cvetan
    "extract the profile of Bruno's thesis" in {
      println("\n\n\n")
      val A: HOLFormula = Atom(new ConstantStringSymbol("A"), List())
      val B: HOLFormula = Atom(new ConstantStringSymbol("B"), List())
      val C: HOLFormula = Atom(new ConstantStringSymbol("C"), List())


      val ax1 = Axiom(A::Nil, A::Nil)
      val ax2 = Axiom(B::Nil, B::Nil)
      val ax3 = Axiom(B::Nil, B::Nil)
      val ax4 = Axiom(A::Nil, A::Nil)
      val ax5 = Axiom(C::Nil, C::Nil)
//      val ax6 = Axiom(Sequent(C::Nil, C::Nil))(PointerFOFactoryInstance)ExactBound(1)
      val r1 = AndRightRule(ax1,ax2,A,B)//.asInstanceOf[LKProof]
      var r2 = AndLeftRule(r1,A,B)
      val r3 = AndRightRule(ax3,ax4,B,A)
      var r4 = AndLeftRule(r3,A,B)
      val r5 = CutRule(r2,r4, And(A,B))
      val r6 = ax5//CutRule(ax5,ax6, C)
      val proof = OrLeftRule(r5,r6, And(A,B), C)

      val s = StructCreators.extract( proof )
      val prf = deleteTautologies(proofProfile(s, proof).map( _.toFSequent ))
      val cs = StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent )

      // specs2 require a least one Result, see org.specs2.specification.Example 
      Success()
      // TODO: check if profile is really as expected.
    }
*/

    "introduce a cut and eliminate it via Gentzen in the LinearExampleProof (n = 4)" in {
      if (!(new MiniSATProver).isInstalled()) skipped("MiniSAT is not installed")

      val p = LinearExampleProof( 0, 4 )
      val pi = CutIntroduction.one_cut_one_quantifier(p, false)
      val pe = ReductiveCutElim.eliminateAllByUppermost(pi, steps = false)

      ReductiveCutElim.isCutFree(p)  must beEqualTo( true )
      ReductiveCutElim.isCutFree(pi) must beEqualTo( false )
      ReductiveCutElim.isCutFree(pe) must beEqualTo( true )
    }


    "load veriT proofs pi and verify the validity of Deep(pi) using MiniSAT" in {

      if (!(new MiniSATProver).isInstalled()) skipped("MiniSAT is not installed")

      for (i <- List(0,1,3)) { // Tests 2 and 4 take comparatively long.
        val p = VeriTParser.getExpansionProof(tempCopyOfClasspathFile(s"test${i}.verit")).get
        val seq = ETtoDeep(p)

        /*
        println("file: " +testfilename)
        println("formula: " +seq)
        */
        (new at.logic.provers.minisat.MiniSATProver).isValid(seq) must beTrue
      }
      ok
    }

    "load Prover9 proof, extract expansion tree and check that deep formula is quasi-tautology using veriT" in {
      skipped("VeriT fails to proof this (at least on some systems)")

      val veriT = new VeriTProver()

      if (!veriT.isInstalled()) skipped("VeriT is not installed")

      for (testBaseName <- "ALG138+1.out" :: Nil) {
        // TODO: add cade13example.out once tptpfolexporter issues are sorted out

        val testFilePath = "target" + separator + testBaseName

        val (resProof, seq, _) = Prover9.parse_prover9(testFilePath)
        val lkProof = new Prover9Prover().getLKProof(seq).get

        val expansionSequent = extractExpansionSequent(lkProof, false)

        val seqToProve = ETtoDeep(expansionSequent)

        /*
        println("file: " +testfilename)
        println("formula: " +seq)
        */

        veriT.isValid(seqToProve) must beEqualTo (true)
      }
      ok
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

    "load Prover9 proof without equality reasoning, extract expansion tree E, verify deep formula of E with minisat" in {
      if (!(new MiniSATProver).isInstalled()) skipped("MiniSAT is not installed")
      for (testBaseName <- "PUZ002-1.out" :: Nil) {
        val (resproof, endsequent, _) = Prover9.parse_prover9( tempCopyOfClasspathFile( testBaseName ))

        val closure = FSequent(endsequent.antecedent.map(x => univclosure(x.asInstanceOf[FOLFormula])),
          endsequent.succedent.map(x => existsclosure(x.asInstanceOf[FOLFormula])))
        val clause_set = CNFn(endsequent.toFormula).map(c => FSequent(c.neg.map(f => f.asInstanceOf[FOLFormula]),
          c.pos.map(f => f.asInstanceOf[FOLFormula]))).toList

        val lkproof1 = RobinsonToLK( fixDerivation( resproof, clause_set ), closure )

        val expseq = extractExpansionSequent( lkproof1, false )

        val deep = ETtoDeep( expseq ).toFormula

        (new at.logic.provers.minisat.MiniSATProver).isValid( deep ) must beTrue

        // the next line should work but does not (see issue 279)
        // val lkproof2 = solve.expansionProofToLKProof( ETtoShallow( expseq ), expseq )
      }
      ok
    }
  }
}
