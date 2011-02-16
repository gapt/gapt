package at.logic.simple_schema_test

import at.logic.calculi.lk.base._
import org.specs.SpecificationWithJUnit
import at.logic.language.schema._
import at.logic.calculi.slk._
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.occurrences.positions._

class SchemaClauseSetTest extends SpecificationWithJUnit {
  "SchemaClauseSetTest" should {

    //--  Create LKS proof (Alex's example) --//
    val i = IntVar(new VariableStringSymbol("i"))
    val n = IntVar(new VariableStringSymbol("n"))
    val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
    val and_1_n_ai = BigAnd(i, ai,Succ(IntZero()), n)
    val and_1_sn_ai = BigAnd(i, ai,Succ(IntZero()), Succ(n))
    val or_1_n_not_ai = BigOr(i, Neg(ai), Succ(IntZero()), n)
    val or_1_sn_not_ai = BigOr(i, Neg(ai), Succ(IntZero()), Succ(n))

    val psi = SchemaProofLinkRule(Sequent(and_1_n_ai::Or(or_1_n_not_ai,
      IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil))::Nil, and_1_sn_ai::Nil), "psi_n+1", Succ(n)::Nil)
    val xi = SchemaProofLinkRule(Sequent(and_1_sn_ai::or_1_sn_not_ai::Nil, Nil), "psi_n+1", Succ(n)::Nil)
    val varPhi_n = CutRule(psi, NegRightRule(xi, or_1_sn_not_ai), and_1_sn_ai)

    "construct correct LKS proof" in {
      varPhi_n must beLike {case x : LKProof => true}
      println(varPhi_n.toString)
    }

  }
}