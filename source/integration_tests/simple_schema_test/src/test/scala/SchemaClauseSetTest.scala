package at.logic.simple_schema_test

import at.logic.calculi.lk.macroRules.AndLeftRule
import at.logic.calculi.lk.base._
import at.logic.language.schema._
import at.logic.calculi.slk._
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.occurrences._
import at.logic.transformations.ceres.struct._

import org.specs.SpecificationWithJUnit

class SchemaClauseSetTest extends SpecificationWithJUnit {
  "SchemaClauseSetTest" should {
     implicit val factory = PointerFOFactoryInstance
    //--  Create LKS proof (Alex's example) --//

    //-- Some formula definitions
    val i = IntVar(new VariableStringSymbol("i"))
    val n = IntVar(new VariableStringSymbol("n"))
    val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
    val a1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(IntZero())::Nil)
    val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
    val and_1_n_ai = BigAnd(i, ai,Succ(IntZero()), n)
    val and_1_sn_ai = BigAnd(i, ai,Succ(IntZero()), Succ(n))
    val or_1_n_not_ai = BigOr(i, Neg(ai), Succ(IntZero()), n)
    val or_1_sn_not_ai = BigOr(i, Neg(ai), Succ(IntZero()), Succ(n))
    // end of formula definitions --//

     //-- Some subproofs of varPhi_n proof
    val psi = SchemaProofLinkRule(Sequent(and_1_n_ai::Or(or_1_n_not_ai,
      IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil))::Nil, and_1_sn_ai::Nil), "psi", Succ(n)::Nil)
    val xi = SchemaProofLinkRule(Sequent(and_1_sn_ai::or_1_sn_not_ai::Nil, Nil), "xi", Succ(n)::Nil)
    val p = NegRightRule(xi, or_1_sn_not_ai)
    // end of subproofs of varPhi_n proof --//

    val varPhi_n = CutRule(psi, p, and_1_sn_ai)

    "construct correct LKS proof" in {
      varPhi_n must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      varPhi_n.root.getSequent must beEqual(
        Sequent(and_1_n_ai::Or(or_1_n_not_ai, a_sn)::Nil, Neg(or_1_sn_not_ai)::Nil) )
    }

    val xi_1 = NegLeftRule(Axiom(Sequent(a1::Nil, a1::Nil)), a1)

    "construct correct LKS proof" in {
      xi_1 must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      xi_1.root.getSequent must beEqual( Sequent(a1::Neg(a1)::Nil, Nil) )
    }

    //-- Some subproofs of xi_sn proof
    val x1 = NegLeftRule(Axiom(Sequent(a_sn::Nil, a_sn::Nil)), a_sn)
    val x2 = SchemaProofLinkRule(Sequent(and_1_n_ai::or_1_n_not_ai::Nil, Nil), "xi", n::Nil)
    val x3 = OrLeftRule(x2, x1, or_1_n_not_ai, Neg(a_sn))
    val x4 = OrEquivalenceRule1(x3, x3.prin.head, or_1_sn_not_ai)
    val x5 = AndLeftRule(x4, and_1_n_ai, a_sn)
    // end of subproofs of xi_sn proof --//

    val xi_sn = AndEquivalenceRule1(x5, x5.prin.head, and_1_sn_ai)

    "construct correct LKS proof" in {
      xi_sn must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      xi_sn.root.getSequent must beEqual( Sequent(and_1_sn_ai::or_1_sn_not_ai::Nil, Nil) )
    }

    val phi_1 = Axiom(Sequent(a1::Nil, a1::Nil))

    "construct correct LKS proof" in {
      phi_1 must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      phi_1.root.getSequent must beEqual( Sequent(a1::Nil, a1::Nil) )
    }

    //-- Some subproofs of phi_sn proof
    val y1 = AndRightRule(SchemaProofLinkRule(Sequent(and_1_n_ai::Nil, and_1_n_ai::Nil), "phi", n::Nil),
      Axiom(Sequent(a_sn::Nil, a_sn::Nil)), and_1_n_ai, a_sn)
    val y2 = AndEquivalenceRule1(y1, y1.prin.head, and_1_sn_ai)
    val y3 = AndLeftRule(y2, and_1_n_ai, a_sn)
    // end of subproofs of phi_sn proof --//

    val phi_sn = AndEquivalenceRule1(y3, y3.prin.head, and_1_sn_ai)

    "construct correct LKS proof" in {
      phi_sn must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      phi_sn.root.getSequent must beEqual(
        Sequent(and_1_sn_ai::Nil, and_1_sn_ai::Nil) )
    }

    //-- Some subproofs of psi_sn proof
    val z1 = OrLeftRule(x2, Axiom(Sequent(a_sn::Nil, a_sn::Nil)), or_1_n_not_ai, a_sn)
    val z2 = AndRightRule(SchemaProofLinkRule(Sequent(and_1_n_ai::Nil, and_1_n_ai::Nil), "phi", n::Nil),
      z1, and_1_n_ai, a_sn)
    val z3 = AndEquivalenceRule1(z2, z2.prin.head, and_1_sn_ai)
    // end of subproofs of psi_sn proof --//

    val psi_sn = ContractionLeftRule(z3, and_1_n_ai)

    "construct correct LKS proof" in {
      psi_sn must beLike {case x : LKProof => true}
    }
    "check that it has correct end-sequent" in {
      psi_sn.root.getSequent must beEqual(
        Sequent(and_1_n_ai::Or(or_1_n_not_ai, a_sn)::Nil, and_1_sn_ai::Nil) )
    }
  }

  "extract a schema clause set from a simple proof" in {
    val i = IntVar(new VariableStringSymbol("i"))
    val n = IntVar(new VariableStringSymbol("n"))
    val p0 = IndexedPredicate(new ConstantStringSymbol("p"), IntZero()::Nil)
    val pi = IndexedPredicate(new ConstantStringSymbol("p"), i::Nil)

    // base
    val ax = Axiom( Sequent(p0::Nil, p0::Nil) )
    val base = AndEquivalenceRule3(ax, p0, BigAnd(i, pi, IntZero(), IntZero() ) )

    // step
    val psn = IndexedPredicate(new ConstantStringSymbol("p"), Succ(n)::Nil)
    val f1 = And( BigAnd( i, pi, IntZero(), n ), psn )
    val link = SchemaProofLinkRule(Sequent( f1::Nil, p0::Nil ), "varphi", n::Nil )
    val f2 = BigAnd( i, pi, IntZero(), Succ(n) )
    val step = AndEquivalenceRule1( link, f1, f2 )

    SchemaProofDB.put( new SchemaProof( "varphi", n::Nil, base, step ) )
    //println( StructCreators.extract( "varphi" ) )
  }
}
