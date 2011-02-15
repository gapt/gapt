package at.logic.language.schema

import _root_.at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}
import org.specs.SpecificationWithJUnit

class SchemaTest extends SpecificationWithJUnit {
  "Schema" should {
    val i = IntVar(new VariableStringSymbol("i"))
    val one = Succ(IntZero())
    val two = Succ(Succ(IntZero()))
    val p = new ConstantStringSymbol("P")
    val p1 = IndexedPredicate(p, one::Nil)
    val p2 = IndexedPredicate(p, two::Nil)

    "create IndexedPredicate correctly (1)" in {
      (p1) must beLike {case f: SchemaFormula => true}
    }
    "create IndexedPredicate correctly (2)" in {
      (p2) must beLike {case f: SchemaFormula => true}
    }

    "create SchemaFormula correctly" in {
      val and = And(p1, p2)
      (and) must beLike {case f: SchemaFormula => true}
    }
  }
}