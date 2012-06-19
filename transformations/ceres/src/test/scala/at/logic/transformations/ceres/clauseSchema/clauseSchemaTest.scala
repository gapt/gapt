package at.logic.transformations.ceres.clauseSchema

import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.propositionalRules.{Axiom, NegLeftRule}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.hol.{HOLExpression, HOLFormula}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.parsing.language.simple.SHLK
import at.logic.transformations.ceres.projections.printSchemaProof
import java.io.File.separator
import scala.io._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class clauseSchemaTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  import at.logic.language.schema._
  "clauseSchemaTest" should {
    "create a correct schema clause" in {
      println(Console.RED+"\n\n       clauseSchemaTest\n\n"+Console.RESET)
      val k = IntVar(new VariableStringSymbol("k"))
      val real_n = IntVar(new VariableStringSymbol("n"))
      val n = k
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
      val s = Set[FormulaOccurrence]()

      val i = IntVar(new VariableStringSymbol("i"))
      val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
      val B = IndexedPredicate(new ConstantStringSymbol("B"), i)
      val C = IndexedPredicate(new ConstantStringSymbol("C"), i)
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
      val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
      val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
      val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)

      val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
      val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
      val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
      val orneg = at.logic.language.schema.Or(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

      val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))

      val Pk = IndexedPredicate(new ConstantStringSymbol("P"), k)
      val P0 = IndexedPredicate(new ConstantStringSymbol("P"), IntZero())
      val Q0 = IndexedPredicate(new ConstantStringSymbol("Q"), IntZero())
      val Pk1 = IndexedPredicate(new ConstantStringSymbol("P"), Succ(k))
      val c0 = nonVarSclause(List.empty[HOLFormula], P0::Nil)
      val ck1 = nonVarSclause(List.empty[HOLFormula], Pk1::Nil)
      val X = sClauseVar("X")
      val base: sClause = sClauseComposition(c0, X)
      val rec: sClause = sClauseComposition(ck1, X)
      val clause_schema = ClauseSchema(base, rec)
      println(base)
      val non = nonVarSclause(Q0::Nil, List.empty[HOLFormula])
      val map = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], non)

      val rez = clause_schema(two, map)
      println("\nrez = "+rez)
      println("\n\n\n")
//      println(normalizeSClause(sClauseComposition(rez, X)))
      println(Pred(two))
      println("\n\n\n\n")
      ok
    }
  }
}

