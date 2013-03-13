package at.logic.simple_schema_test

import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.propositionalRules.{Axiom, NegLeftRule}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.schema.{And => AndS, Or => OrS, Neg => NegS, Imp => ImpS, _}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success
import at.logic.language.lambda.types.Ti
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.shlk._
import at.logic.gui.prooftool.gui.Main
import scala.io._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import at.logic.algorithms.lk.{CleanStructuralRules, solvePropositional}


@RunWith(classOf[JUnitRunner])
class autoPropositionalTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  "SolvePropositionalTest" should {
    "solve the sequents" in {
      //println(Console.GREEN+"\n\n\nintegration_tests/SolvePropositionalTest.scala \n\n\n"+Console.RESET)
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

      val B0 = IndexedPredicate(new ConstantStringSymbol("B"), IntZero())

      val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
      val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
      val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
      val orneg = OrS(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

      val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
      val An = IndexedPredicate(new ConstantStringSymbol("A"), k)
      val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
      val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
      val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)

      val biga = BigAnd(i, A, zero, one)
      val bigo = BigOr(i, A, zero, one)
      val biga2 = BigAnd(i, A, zero, two)
      val bigo2 = BigOr(i, A, zero, two)

      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)

      val p = solvePropositional(fseq)

      // TODO: something with these...
      solvePropositional(FSequent(Neg(And(Neg(A), Neg(B))) :: Nil, Or(A , B) :: Nil))
      solvePropositional(FSequent(Or(Or(A, B), C) :: Nil, A :: B :: C :: Nil))
      solvePropositional(FSequent(And(A , B) :: Nil, Neg(Or(Neg(A), Neg(B))) :: Nil))
      solvePropositional(FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil))
      solvePropositional(FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil))
      solvePropositional(FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil))

      val c2 = HOLConst(new ConstantStringSymbol("c"), Ti())
      val d2 = HOLConst(new ConstantStringSymbol("d"), Ti())
      val e2 = HOLConst(new ConstantStringSymbol("e"), Ti())
      val Pc2 = Atom(new ConstantStringSymbol("P"), c2::Nil)
      val Pd2 = Atom(new ConstantStringSymbol("P"), d2::Nil)
      val Pe2 = Atom(new ConstantStringSymbol("P"), e2::Nil)
      val andPc2Pd2 = And(Pc2, Pd2)
      val impPc2Pd2 = Imp(Pc2, Pd2)
      val imp_andPc2Pd2_Pe2 = Imp(andPc2Pd2, Pe2)
      val orPc2Pd2 = Or(Pc2, Pd2)
      val seq11 = FSequent(Pc2::Nil, Pc2::Nil)
      val seq12 = FSequent(andPc2Pd2::Nil, Pc2::Nil)
      val seq13 = FSequent(Pc2::Nil, orPc2Pd2::Nil)
      val seq14 = FSequent(andPc2Pd2::Nil, orPc2Pd2::Nil)
      val seq15 = FSequent(Pc2::impPc2Pd2::imp_andPc2Pd2_Pe2::Nil, Pe2::Nil)
      val seq16 = FSequent(Pc2::Nil, Pd2::Nil)
      val seq17 = FSequent(Imp(A,B)::Imp(B,C)::Nil, Imp(A,C)::Nil)

//      solvePropositional(seq16) must beEqualTo (None)

      val proof = solvePropositional.prove(seq17).get
      val min_proof = CleanStructuralRules(proof)
//      printSchemaProof(proof)
//      Main.display("proof",proof)
//      Main.display("min_proof",min_proof)
//      while(true) {}
      ok
    }
  }
}

