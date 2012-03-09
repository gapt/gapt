package at.logic.transformations.ceres.autoprop

import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.propositionalRules.{Axiom, NegLeftRule}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.HOLFormula
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.transformations.ceres.projections.printSchemaProof
import java.io.File.separator
import scala.io._
import org.specs.SpecificationWithJUnit

class autopropTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  import at.logic.language.schema._
  "autopropTest" should {
    "continue autopropositional" in {
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
      val orneg = at.logic.language.schema.Or(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

      val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
      val An = IndexedPredicate(new ConstantStringSymbol("A"), k)
      val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
      val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
      val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
//             println("\n\n START \n\n")

//      val fseq = FSequent(A0 :: Nil, A0 :: Nil)
//      val fseq = FSequent(A0 :: Neg(A0) :: Nil, Nil)
      val biga = BigAnd(i, A, zero, one)
      val bigo = BigOr(i, A, zero, one)
      val biga2 = BigAnd(i, A, zero, two)
      val bigo2 = BigOr(i, A, zero, two)

//      val fseq = FSequent(bigo :: Nil, A0 :: A1 :: Nil )
//      val fseq = FSequent(biga :: Nil, A0 :: A1 :: Nil )
//      val fseq = FSequent(biga :: Nil, A0 :: A1 :: A2 :: Nil )
//      val fseq = FSequent(A :: B :: Nil, And(A, B) :: Nil)
//      val fseq = FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil)
//      val fseq = FSequent(A0 :: A1 :: Nil, biga :: Nil)
//        val fseq = FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil)

//      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)
      val fseq = FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil)

//      val fseq = FSequent(And(A , B) :: Nil, Neg(Or(Neg(A), Neg(B))) :: Nil)
//      val fseq = FSequent(Neg(And(Neg(A), Neg(B))) :: Nil, Or(A , B) :: Nil)


//      val fseq = FSequent(Or(Or(A, B), C) :: Nil, A :: B :: C :: Nil)


      val p = Autoprop.apply1(fseq)
      println(Console.RED+"\n\n\nautopropositional : "+Console.RESET+printSchemaProof.sequentToString(p.root) )
      println("\n\n\nautopropositional, size = "+rulesNumber(p))
      printSchemaProof(p)

      val p1 = StructuralOptimizationAfterAutoprop(p)
      println("\n\n\niteration 1, size = :"+rulesNumber(p1))
      printSchemaProof(p1)
//
      val p2 = StructuralOptimizationAfterAutoprop(p1)
      println("\n\n\niteration 2, size = :"+rulesNumber(p2))
      printSchemaProof(p2)
////
      val p3 = StructuralOptimizationAfterAutoprop(p2)
      println("\n\n\niteration 3, size = :"+rulesNumber(p3))
      printSchemaProof(p3)
      println("\n\n")

      val p4 = StructuralOptimizationAfterAutoprop(p3)
      println("\n\n\niteration 3, size = :"+rulesNumber(p4))
      printSchemaProof(p4)
      println("\n\n")

      val p5 = StructuralOptimizationAfterAutoprop(p4)
      println("\n\n\niteration 3, size = :"+rulesNumber(p5))
      printSchemaProof(p5)
      println("\n\n")

//      val pauto = Autoprop(fseq)
//      println("\n\n\nautoprop minimal form, size = "+rulesNumber(pauto))
//      printSchemaProof(pauto)
//      println("\n\n")

      Autoprop(FSequent(Neg(And(Neg(A), Neg(B))) :: Nil, Or(A , B) :: Nil))
      Autoprop(FSequent(Or(Or(A, B), C) :: Nil, A :: B :: C :: Nil))
      Autoprop(FSequent(And(A , B) :: Nil, Neg(Or(Neg(A), Neg(B))) :: Nil))
      Autoprop(FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil))
      Autoprop(FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil))
      Autoprop(FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil))
    }
  }
}

