package at.logic.simple_schema_test

import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.writers.FileWriter
import at.logic.calculi.lk.macroRules.AndLeftRule
import at.logic.calculi.lk.base._
import at.logic.language.schema._
import at.logic.calculi.slk._
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.occurrences._
import at.logic.transformations.ceres.struct._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import java.io.File.separator

import org.specs.SpecificationWithJUnit

class SchemaClauseSetTest extends SpecificationWithJUnit {
  "SchemaClauseSetTest" should {
     implicit val factory = PointerFOFactoryInstance
    //--  Create LKS proof (Alex's example) --//

    //-- Some formula definitions
    val i = IntVar(new VariableStringSymbol("i"))
    val n = IntVar(new VariableStringSymbol("k"))
    val k = IntVar(new VariableStringSymbol("n"))
    val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
    val a0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero()::Nil)
    val a1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(IntZero())::Nil)
    val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
    val a_ssn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(Succ(n))::Nil)
    val and_0_0_ai = BigAnd(i, ai,IntZero(),IntZero())
    val and_0_1_ai = BigAnd(i, ai,IntZero(), Succ(IntZero()))
    val and_0_n_ai = BigAnd(i, ai,IntZero(), n)
    val and_0_sn_ai = BigAnd(i, ai,IntZero(), Succ(n))
    val and_0_ssn_ai = BigAnd(i, ai,IntZero(), Succ(Succ(n)))
    val or_0_0_not_ai = BigOr(i, Neg(ai), IntZero(), IntZero())
    val or_0_1_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(IntZero()))
    val or_0_n_not_ai = BigOr(i, Neg(ai), IntZero(), n)
    val or_0_sn_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(n))
    val or_0_ssn_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(Succ(n)))
    // end of formula definitions --//

     //-- Some subproofs of varPhi_0 proof
    val psi0 = SchemaProofLinkRule(Sequent(and_0_0_ai::Or(or_0_0_not_ai, a1)::Nil, and_0_1_ai::Nil),
        "\\psi", Succ(IntZero())::Nil)
    val xi0 = SchemaProofLinkRule(Sequent(and_0_1_ai::or_0_1_not_ai::Nil, Nil), "\\xi", Succ(IntZero())::Nil)
    val p0 = NegRightRule(xi0, or_0_1_not_ai)
    // end of subproofs of varPhi_0 proof --//

    val varPhi_0 = CutRule(psi0, p0, and_0_1_ai)

    "construct correct LKS proof" in {
      varPhi_0 must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      varPhi_0.root.getSequent must beEqual(
        Sequent(and_0_0_ai::Or(or_0_0_not_ai, a1)::Nil, Neg(or_0_1_not_ai)::Nil) )
    }

     //-- Some subproofs of varPhi_n proof
    val psi = SchemaProofLinkRule(Sequent(and_0_sn_ai::Or(or_0_sn_not_ai, a_ssn)::Nil, and_0_ssn_ai::Nil),
        "\\psi", Succ(n)::Nil)
    val xi = SchemaProofLinkRule(Sequent(and_0_ssn_ai::or_0_ssn_not_ai::Nil, Nil), "\\xi", Succ(Succ(n))::Nil)
    val p = NegRightRule(xi, or_0_ssn_not_ai)
    // end of subproofs of varPhi_n proof --//

    val varPhi_sn = CutRule(psi, p, and_0_ssn_ai)

    "construct correct LKS proof" in {
      varPhi_sn must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      varPhi_sn.root.getSequent must beEqual(
        Sequent(and_0_sn_ai::Or(or_0_sn_not_ai, a_ssn)::Nil, Neg(or_0_ssn_not_ai)::Nil) )
    }

    //-- Some subproofs of xi_0 proof
    val x01 = AndEquivalenceRule3(Axiom(Sequent(a0::Nil, a0::Nil)), a0, and_0_0_ai)
    val x02 = NegLeftRule(x01, a0)
    // end of subproofs of xi_0 proof --//

    val xi_0 = OrEquivalenceRule3(x02, x02.prin.head, or_0_0_not_ai)

    "construct correct LKS proof" in {
      xi_0 must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      xi_0.root.getSequent must beEqual( Sequent(and_0_0_ai::or_0_0_not_ai::Nil, Nil) )
    }

    //-- Some subproofs of xi_sn proof
    val x1 = NegLeftRule(Axiom(Sequent(a_sn::Nil, a_sn::Nil)), a_sn)
    val x2 = SchemaProofLinkRule(Sequent(and_0_n_ai::or_0_n_not_ai::Nil, Nil), "\\xi", n::Nil)
    val x3 = OrLeftRule(x2, x1, or_0_n_not_ai, Neg(a_sn))
    val x4 = OrEquivalenceRule1(x3, x3.prin.head, or_0_sn_not_ai)
    val x5 = AndLeftRule(x4, and_0_n_ai, a_sn)
    // end of subproofs of xi_sn proof --//

    val xi_sn = AndEquivalenceRule1(x5, x5.prin.head, and_0_sn_ai)

    "construct correct LKS proof" in {
      xi_sn must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      xi_sn.root.getSequent must beEqual( Sequent(and_0_sn_ai::or_0_sn_not_ai::Nil, Nil) )
    }

    //-- Some subproofs of phi_0 proof
    val y0 = AndEquivalenceRule3(Axiom(Sequent(a0::Nil, a0::Nil)), a0, and_0_0_ai)
    // end of subproofs of phi_sn proof --//

    val phi_0 = AndEquivalenceRule3(y0, a0, and_0_0_ai)

    "construct correct LKS proof" in {
      phi_0 must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      phi_0.root.getSequent must beEqual( Sequent(and_0_0_ai::Nil, and_0_0_ai::Nil) )
    }

    //-- Some subproofs of phi_sn proof
    val y1 = AndRightRule(SchemaProofLinkRule(Sequent(and_0_n_ai::Nil, and_0_n_ai::Nil), "\\phi", n::Nil),
      Axiom(Sequent(a_sn::Nil, a_sn::Nil)), and_0_n_ai, a_sn)
    val y2 = AndEquivalenceRule1(y1, y1.prin.head, and_0_sn_ai)
    val y3 = AndLeftRule(y2, and_0_n_ai, a_sn)
    // end of subproofs of phi_sn proof --//

    val phi_sn = AndEquivalenceRule1(y3, y3.prin.head, and_0_sn_ai)

    "construct correct LKS proof" in {
      phi_sn must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      phi_sn.root.getSequent must beEqual(
        Sequent(and_0_sn_ai::Nil, and_0_sn_ai::Nil) )
    }

    //-- Some subproofs of psi_0 proof
    val z01 = OrLeftRule(SchemaProofLinkRule(Sequent(and_0_0_ai::or_0_0_not_ai::Nil, Nil), "\\xi", IntZero()::Nil),
      Axiom(Sequent(a1::Nil, a1::Nil)), or_0_0_not_ai, a1)
    val z02 = AndRightRule(SchemaProofLinkRule(Sequent(and_0_0_ai::Nil, and_0_0_ai::Nil), "\\phi", IntZero()::Nil),
      z01, and_0_0_ai, a1)
    val z03 = AndEquivalenceRule1(z02, z02.prin.head, and_0_1_ai)
    // end of subproofs of psi_0 proof --//

    val psi_0 = ContractionLeftRule(z03, and_0_0_ai)

    "construct correct LKS proof" in {
      psi_0 must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      psi_0.root.getSequent must beEqual(
        Sequent(and_0_0_ai::Or(or_0_0_not_ai, a1)::Nil, and_0_1_ai::Nil) )
    }

    //-- Some subproofs of psi_sn proof
    val z1 = OrLeftRule(SchemaProofLinkRule(Sequent(and_0_sn_ai::or_0_sn_not_ai::Nil, Nil), "\\xi", Succ(n)::Nil),
      Axiom(Sequent(a_ssn::Nil, a_ssn::Nil)), or_0_sn_not_ai, a_ssn)
    val z2 = AndRightRule(SchemaProofLinkRule(Sequent(and_0_sn_ai::Nil, and_0_sn_ai::Nil), "\\phi", Succ(n)::Nil),
      z1, and_0_sn_ai, a_ssn)
    val z3 = AndEquivalenceRule1(z2, z2.prin.head, and_0_ssn_ai)
    // end of subproofs of psi_sn proof --//

    val psi_sn = ContractionLeftRule(z3, and_0_sn_ai)

    "construct correct LKS proof" in {
      psi_sn must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      psi_sn.root.getSequent must beEqual(
        Sequent(and_0_sn_ai::Or(or_0_sn_not_ai, a_ssn)::Nil, and_0_ssn_ai::Nil) )
    }

    "extract a schema clause set from varPhi_n" in {
      SchemaProofDB.clear
      SchemaProofDB.put( new SchemaProof( "\\xi", n::Nil,
        new Sequent(and_0_n_ai::or_0_n_not_ai::Nil, Nil),
        xi_0, xi_sn ) )
      SchemaProofDB.put( new SchemaProof( "\\phi", n::Nil,
        new Sequent(and_0_n_ai::Nil, and_0_n_ai::Nil),
        phi_0, phi_sn ) )
      SchemaProofDB.put( new SchemaProof( "\\psi", n::Nil,
        new Sequent(and_0_n_ai::Or(or_0_n_not_ai, a_sn)::Nil, and_0_sn_ai::Nil),
        psi_0, psi_sn ))
      SchemaProofDB.put( new SchemaProof( "\\varphi", n::Nil,
        new Sequent(and_0_n_ai::Or(or_0_n_not_ai, a_sn)::Nil, Neg(or_0_sn_not_ai)::Nil),
        varPhi_0, varPhi_sn ) )
      val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extractStruct( "\\varphi", k ) )
      (new FileWriter("target" + separator + "test-classes" + separator + "cs_ex1.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
        .exportSequentList(cs.map(so => so.getSequent), Nil).close
    }

    "extract a schema clause set from a simple proof" in {
      val p0 = IndexedPredicate(new ConstantStringSymbol("p"), IntZero()::Nil)
      val pi = IndexedPredicate(new ConstantStringSymbol("p"), i::Nil)

      // base
      val ax = Axiom( Sequent(p0::Nil, p0::Nil) )
      val base = AndEquivalenceRule3(ax, p0, BigAnd(i, pi, IntZero(), IntZero() ) )

      // step
      val f0 = BigAnd( i, pi, IntZero(), n )
      val psk = IndexedPredicate(new ConstantStringSymbol("p"), Succ(n)::Nil)
      val f1 = And( f0, psk )
      val link = SchemaProofLinkRule(Sequent( f0::Nil, p0::Nil ), "\\varphi", n::Nil )
      val p1 = AndLeft1Rule(link, f0, psk)
      val f2 = BigAnd( i, pi, IntZero(), Succ(n) )
      val step = AndEquivalenceRule1( p1, f1, f2 )
      SchemaProofDB.clear
      SchemaProofDB.put( new SchemaProof( "\\varphi", n::Nil,
        new Sequent(f0::Nil, p0::Nil),
        base, step ) )
      val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extractStruct( "\\varphi", k ) )
      (new FileWriter("target" + separator + "test-classes" + separator + "cs_simple.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
        .exportSequentList(cs.map(so => so.getSequent), Nil).close

      val f = StructCreators.extractFormula("\\varphi", k)
      (new FileWriter("target" + separator + "test-classes" + separator + "formula.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(Sequent(Nil, f::Nil)::Nil, Nil).close
    }
  }
}
