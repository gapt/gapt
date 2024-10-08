package gapt.integration_tests

import gapt.cutintro._
import gapt.examples.sequence.LinearExampleProof
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLVar
import gapt.formats.ClasspathInputFile
import gapt.formats.StringInputFile
import gapt.formats.llk.LLKProofParser
import gapt.formats.verit.VeriTParser
import gapt.grammars.DeltaTableMethod
import gapt.proofs._
import gapt.proofs.expansion.ExpansionProofToLK
import gapt.proofs.expansion.eliminateCutsET
import gapt.proofs.expansion.RichExpansionSequent
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.transformations.cutNormal
import gapt.proofs.lk.transformations.eliminateDefinitions
import gapt.proofs.lk.transformations.skolemizeLK
import gapt.proofs.lk.util.AtomicExpansion
import gapt.proofs.lk.util.isCutFree
import gapt.proofs.lk.util.regularize
import gapt.proofs.lk.util.solvePropositional
import gapt.provers.prover9.Prover9
import gapt.provers.prover9.Prover9Importer
import gapt.provers.sat.Sat4j
import gapt.provers.verit.VeriT
import org.specs2.mutable._

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
      val p = LinearExampleProof(4)
      CutIntroduction(p, method = DeltaTableMethod()) must beSome
    }

    "introduce a cut and eliminate it via Gentzen in the LinearExampleProof (n = 9)" in {
      val p = LinearExampleProof(9)
      val Some(pi) = CutIntroduction(p, method = DeltaTableMethod()): @unchecked
      val pe = cutNormal(pi)

      isCutFree(p) must beEqualTo(true)
      isCutFree(pi) must beEqualTo(false)
      isCutFree(pe) must beEqualTo(true)
    }

    "load Prover9 proof without equality reasoning, introduce a cut and eliminate it via Gentzen" in {
      if (!Prover9.isInstalled) skipped("Prover9 is not installed")

      val p1 = lkProofFromClasspath("SYN726-1.out")
      val Some(p2) = CutIntroduction(p1, method = DeltaTableMethod()): @unchecked
      val p3 = cutNormal(p2)

      isCutFree(p2) must beEqualTo(false)
      isCutFree(p3) must beEqualTo(true)
    }

    "extract expansion tree from tape proof" in {
      val db = LLKProofParser(ClasspathInputFile("tape3.llk"))
      // I have no idea why, but this makes the code get the correct proof
      val p = db.proof("TAPEPROOF")
      val elp = AtomicExpansion(eliminateDefinitions(db.Definitions)(p))
      val reg = regularize(elp)
      val lksk_proof = skolemizeLK(reg)
      // TODO
      val et = LKToExpansionProof(reg) // must throwA[IllegalArgumentException] // currently contains problematic definitions
      ok
    }

    "construct proof with expansion sequent extracted from proof (1/2)" in {
      val y = FOLVar("y")
      val x = FOLVar("x")
      val Py = FOLAtom("P", y :: Nil)
      val Px = FOLAtom("P", x :: Nil)
      val AllxPx = All(x, Px)

      // test with 1 weak & 1 strong
      val p1 = LogicalAxiom(Py)
      val p2 = ForallLeftRule(p1, AllxPx, y)
      val p3 = ForallRightRule(p2, AllxPx, y)

      val etSeq = eliminateCutsET(LKToExpansionProof(p3))

      val proof = ExpansionProofToLK(etSeq) // must not throw exception
      ok
    }

    "construct proof with expansion sequent extracted from proof (2/2)" in {
      val proof = LinearExampleProof(4)

      val proofPrime = ExpansionProofToLK(eliminateCutsET(LKToExpansionProof(proof))) // must not throw exception
      ok
    }

    "load Prover9 proof without equality reasoning and eliminate cuts via Gentzen" in {
      if (!Prover9.isInstalled) skipped("Prover9 is not installed")

      val p = lkProofFromClasspath("PUZ002-1.out")
      val q = cutNormal(p)

      isCutFree(q) must beEqualTo(true)
    }

    "load veriT proof of reflexivity and verify the validity using sat4j" in {
      val veriTProof =
        """
          |unsat
          |(assume h1 (not (= f_x_0 f_x_0)))
          |(step t2 (cl (= (= f_x_0 f_x_0) true)) :rule eq_simplify)
          |(step t3 (cl (= (not (= f_x_0 f_x_0)) (not true))) :rule cong :premises (t2))
          |(step t4 (cl (= (not true) false)) :rule not_simplify)
          |(step t5 (cl (= (not (= f_x_0 f_x_0)) false)) :rule trans :premises (t3 t4))
          |(step t6 (cl (not (= (not (= f_x_0 f_x_0)) false)) (not (not (= f_x_0 f_x_0))) false) :rule equiv_pos2)
          |(step t7 (cl (not (not (not (= f_x_0 f_x_0)))) (= f_x_0 f_x_0)) :rule not_not)
          |(step t8 (cl (not (= (not (= f_x_0 f_x_0)) false)) (= f_x_0 f_x_0) false) :rule th_resolution :premises (t7 t6))
          |(step t9 (cl false) :rule th_resolution :premises (h1 t5 t8))
          |(step t10 (cl (not false)) :rule false)
          |(step t11 (cl) :rule resolution :premises (t9 t10))
          |""".stripMargin
      val proof = VeriTParser.getExpansionProofWithSymmetry(StringInputFile(veriTProof)).get
      Sat4j.isValid(proof.deep) must beTrue
    }

    "prove quasi-tautology by veriT and verify validity using sat4j (1/2)" in {
      if (!VeriT.isInstalled) skipped("VeriT is not installed")

      val F = hof"a=b -> b=a"
      val E = VeriT.getExpansionProof(HOLSequent(Nil, F :: Nil)).get

      val Edeep = E.deep
      Sat4j.isValid(Edeep) must beTrue
    }

    "prove quasi-tautology by veriT and verify validity using sat4j (2/2)" in {
      if (!VeriT.isInstalled) skipped("VeriT is not installed")

      val C = hof"f(x_0,y_0) = f(y_0,x_0)"
      val AS = hof"f(x_0,y_0)=x_0 -> ( f(y_0,x_0)=y_0 -> x_0=y_0 )"
      val s = HOLSequent(C :: Nil, AS :: Nil)
      val E = VeriT.getExpansionProof(s).get

      val Edeep = E.deep
      Sat4j.isValid(Edeep) must beTrue
    }

    def lkProofFromClasspath(filename: String) =
      Prover9Importer lkProof ClasspathInputFile(filename)

    "load Prover9 proof without equality reasoning, extract expansion sequent E, verify deep formula of E using sat4j and readback E to LK" in {
      if (!Prover9.isInstalled) skipped("Prover9 is not installed")

      val lkproof = lkProofFromClasspath("PUZ002-1.out")
      val expseq = LKToExpansionProof(lkproof)
      val deep = expseq.deep

      Sat4j.isValid(deep) must beTrue

      ExpansionProofToLK(eliminateCutsET(expseq)) // must not throw exception
      ok
    }

    "load Prover9 proof with equality reasoning, extract expansion tree E, verify deep formula of E using veriT" in {
      if (!VeriT.isInstalled) skipped("VeriT is not installed")
      if (!Prover9.isInstalled) skipped("Prover9 is not installed")

      val lkProof = lkProofFromClasspath("ALG004-1.out")
      val expansionSequent = LKToExpansionProof(lkProof)
      val deep = expansionSequent.deep

      VeriT.isValid(deep) must beTrue
    }

    "load Prover9 proof without equality reasoning, extract expansion tree E, verify deep formula of E using solvePropositional" in {
      if (!Prover9.isInstalled) skipped("Prover9 is not installed")

      val lkproof1 = lkProofFromClasspath("PUZ002-1.out")
      val expseq = LKToExpansionProof(lkproof1)
      val deep = expseq.deep

      solvePropositional(deep).isRight must beTrue
    }

    "load Prover9 proof with top and bottom constants, convert it to sequent calculus and extract the deep formula from its expansion sequent" in {
      if (!Prover9.isInstalled) skipped("Prover9 is not installed")
      val lkproof1 = lkProofFromClasspath("NUM484+3.out")
      val expseq = LKToExpansionProof(lkproof1)
      val deep = expseq.deep
      success("everything worked fine")
    }
  }
}
