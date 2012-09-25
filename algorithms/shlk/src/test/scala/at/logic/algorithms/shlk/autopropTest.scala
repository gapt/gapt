package at.logic.algorithms.shlk

import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.propositionalRules.{Axiom, NegLeftRule}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.{Atom, HOLConst, HOLFormula}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
//import at.logic.transformations.ceres.projections.printSchemaProof
import java.io.File.separator
import scala.io._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success
//import at.logic.language.fol.{FOLConst, FOLFactory}
import at.logic.language.lambda.types.Ti


@RunWith(classOf[JUnitRunner])
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

      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)
//      val fseq = FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil)

//      val fseq = FSequent(And(A , B) :: Nil, Neg(Or(Neg(A), Neg(B))) :: Nil)
//      val fseq = FSequent(Neg(And(Neg(A), Neg(B))) :: Nil, Or(A , B) :: Nil)


//      val fseq = FSequent(Or(Or(A, B), C) :: Nil, A :: B :: C :: Nil)


      val p = Autoprop.apply1(fseq) //UNCOMMENT !
//      println(Console.RED+"\n\n\nautopropositional : "+Console.RESET+printSchemaProof.sequentToString(p.root) )
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
//      printSchemaProof(p3)
      println("\n\n")

      val p4 = StructuralOptimizationAfterAutoprop(p3)
      println("\n\n\niteration 4, size = :"+rulesNumber(p4))
//      printSchemaProof(p4)
      println("\n\n")

      val p5 = StructuralOptimizationAfterAutoprop(p4)
      println("\n\n\niteration 5, size = :"+rulesNumber(p5))
//      printSchemaProof(p5)
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
      // specs2 require a least one Result, see org.specs2.specification.Example

//      val c = FOLFactory.createVar(new ConstantStringSymbol("c"), Ti()).asInstanceOf[FOLConst]
//      val Pc = at.logic.language.fol.Atom(new ConstantStringSymbol("P"), c::Nil)
//      val seq = FSequent(Pc::Nil, Pc::Nil)

      println("\n\nHOL Examples")
      val c2 = HOLConst(new ConstantStringSymbol("c"), Ti())
      val d2 = HOLConst(new ConstantStringSymbol("d"), Ti())
      val e2 = HOLConst(new ConstantStringSymbol("e"), Ti())
      val Pc2 = Atom(new ConstantStringSymbol("P"), c2::Nil)
      val Pd2 = Atom(new ConstantStringSymbol("P"), d2::Nil)
      val Pe2 = Atom(new ConstantStringSymbol("P"), e2::Nil)
      val andPc2Pd2 = at.logic.language.hol.And(Pc2, Pd2)
      val impPc2Pd2 = at.logic.language.hol.Imp(Pc2, Pd2)
      val imp_andPc2Pd2_Pe2 = at.logic.language.hol.Imp(andPc2Pd2, Pe2)
      val orPc2Pd2 = at.logic.language.hol.Or(Pc2, Pd2)
      val seq11 = FSequent(Pc2::Nil, Pc2::Nil)
      val seq12 = FSequent(andPc2Pd2::Nil, Pc2::Nil)
      val seq13 = FSequent(Pc2::Nil, orPc2Pd2::Nil)
      val seq14 = FSequent(andPc2Pd2::Nil, orPc2Pd2::Nil)
      val seq15 = FSequent(Pc2::impPc2Pd2::imp_andPc2Pd2_Pe2::Nil, Pe2::Nil)
      val seq16 = FSequent(Pc2::Nil, Pd2::Nil)


//      printSchemaProof(Autoprop(seq11))
//      printSchemaProof(Autoprop(seq12))
//      printSchemaProof(Autoprop(seq13))
//      printSchemaProof(Autoprop(seq14))

      ContinueAutoProp(seq16) must beEqualTo (None)

      Success()
    }
  }
}

// old version
//class autopropTest extends SpecificationWithJUnit {
//  implicit val factory = defaultFormulaOccurrenceFactory
//  import at.logic.language.schema._
//  "autopropTest" should {
//    "continue autopropositional" in {
//      val k = IntVar(new VariableStringSymbol("k"))
//      val real_n = IntVar(new VariableStringSymbol("n"))
//      val n = k
//      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
//      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
//      val s = Set[FormulaOccurrence]()
//
//      val i = IntVar(new VariableStringSymbol("i"))
//      val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
//      val B = IndexedPredicate(new ConstantStringSymbol("B"), i)
//      val C = IndexedPredicate(new ConstantStringSymbol("C"), i)
//      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
//      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
//      val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
//      val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
//      val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)
//
//      val B0 = IndexedPredicate(new ConstantStringSymbol("B"), IntZero())
//
//      val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
//      val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
//      val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
//      val orneg = at.logic.language.schema.Or(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]
//
//      val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
//      val An = IndexedPredicate(new ConstantStringSymbol("A"), k)
//      val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
//      val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
//      val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
//      //             println("\n\n START \n\n")
//
//      //      val fseq = FSequent(A0 :: Nil, A0 :: Nil)
//      //      val fseq = FSequent(A0 :: Neg(A0) :: Nil, Nil)
//      val biga = BigAnd(i, A, zero, one)
//      val bigo = BigOr(i, A, zero, one)
//      val biga2 = BigAnd(i, A, zero, two)
//      val bigo2 = BigOr(i, A, zero, two)
//
//      //      val fseq = FSequent(bigo :: Nil, A0 :: A1 :: Nil )
//      //      val fseq = FSequent(biga :: Nil, A0 :: A1 :: Nil )
//      //      val fseq = FSequent(biga :: Nil, A0 :: A1 :: A2 :: Nil )
//      //      val fseq = FSequent(A :: B :: Nil, And(A, B) :: Nil)
//      //      val fseq = FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil)
//      //      val fseq = FSequent(A0 :: A1 :: Nil, biga :: Nil)
//      //        val fseq = FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil)
//
//      //      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)
//      //      val fseq = FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil)
//
//      //      val fseq = FSequent(And(A , B) :: Nil, Neg(Or(Neg(A), Neg(B))) :: Nil)
//      //      val fseq = FSequent(Neg(And(Neg(A), Neg(B))) :: Nil, Or(A , B) :: Nil)
//
//
//      //      val fseq = FSequent(Or(Or(A, B), C) :: Nil, A :: B :: C :: Nil)
//
//      //      val p = Autoprop.apply1(SHLK.parseSequent(
//      //      val p = Autoprop(
//      //        "(BigAnd(i=0..0) ( (~S(i) \\/ ((((A(i) /\\ ~B(i)) /\\ ~C(i)) \\/ ((~A(i) /\\ B(i)) /\\ ~C(i))) \\/ ((~A(i) /\\ ~B(i)) /\\ C(i)))) /\\ (~((((A(i) /\\ ~B(i)) /\\ ~C(i)) \\/ ((~A(i) /\\ B(i)) /\\ ~C(i))) \\/ ((~A(i) /\\ ~B(i)) /\\ C(i))) \\/ S(i)) )/\\" +
//      //        "(BigAnd(i=0..0) ( (~C(i+1) \\/ (((A(i) /\\ B(i)) \\/ (C(i) /\\ A(i))) \\/ (C(i) /\\ B(i)))) /\\ (~(((A(i) /\\ B(i)) \\/ (C(i) /\\ A(i))) \\/ (C(i) /\\ B(i))) \\/ C(i+1)) )/\\ ~C(0) )), " +
//      //        "(BigAnd(i=0..0) ( (~Sp(i) \\/ ((((A(i) /\\ ~B(i)) /\\ ~Cp(i)) \\/ ((~A(i) /\\ B(i)) /\\ ~Cp(i))) \\/ ((~A(i) /\\ ~B(i)) /\\ Cp(i)))) /\\ (~((((A(i) /\\ ~B(i)) /\\ ~Cp(i)) \\/ ((~A(i) /\\ B(i)) /\\ ~Cp(i))) \\/ ((~A(i) /\\ ~B(i)) /\\ Cp(i))) \\/ Sp(i)) ) /\\ " +
//      //        "(BigAnd(i=0..0) ( (~Cp(i+1) \\/ (((A(i) /\\ B(i)) \\/ (Cp(i) /\\ A(i))) \\/ (Cp(i) /\\ B(i)))) /\\ (~(((A(i) /\\ B(i)) \\/ (Cp(i) /\\ A(i))) \\/ (Cp(i) /\\ B(i))) \\/ Cp(i+1)) )  /\\  ~Cp(0)  ) ) " +
//      //        "|- " +
//      //        "BigAnd(i=0..0) ( (~S(i) \\/ Sp(i)) /\\ (~Sp(i) \\/ S(i)) )").last
//      //
//      //      println("\n\n\n\n\n")
//      //      println (printSchemaProof.sequentToString (p.root))
//      //      val p = Autoprop.apply1(fseq)
//      //      println(Console.RED+"\n\n\nautopropositional : "+Console.RESET+printSchemaProof.sequentToString(p.root) )
//      //      println("\n\n\nautopropositional, size = "+rulesNumber(p))
//      //      printSchemaProof(p)
//
//      //      val p1 = StructuralOptimizationAfterAutoprop(p)
//      //      println("\n\n\niteration 1, size = :"+rulesNumber(p1))
//      //      printSchemaProof(p1)
//      //
//      //      val p2 = StructuralOptimizationAfterAutoprop(p1)
//      //      println("\n\n\niteration 2, size = :"+rulesNumber(p2))
//      //      printSchemaProof(p2)
//      ////
//      //      val p3 = StructuralOptimizationAfterAutoprop(p2)
//      //      println("\n\n\niteration 3, size = :"+rulesNumber(p3))
//      //      printSchemaProof(p3)
//      //      println("\n\n")
//
//      //      val p4 = StructuralOptimizationAfterAutoprop(p3)
//      //      println("\n\n\niteration 3, size = :"+rulesNumber(p4))
//      //      printSchemaProof(p4)
//      //      println("\n\n")
//
//      //      val p5 = StructuralOptimizationAfterAutoprop(p4)
//      //      println("\n\n\niteration 3, size = :"+rulesNumber(p5))
//      //      printSchemaProof(p5)
//      //      println("\n\n")
//
//      //      val pauto = Autoprop(fseq)
//      //      println("\n\n\nautoprop minimal form, size = "+rulesNumber(pauto))
//      //      printSchemaProof(pauto)
//      //      println("\n\n")
//
//      //      Autoprop(FSequent(Neg(And(Neg(A), Neg(B))) :: Nil, Or(A , B) :: Nil))
//      //      Autoprop(FSequent(Or(Or(A, B), C) :: Nil, A :: B :: C :: Nil))
//      //      printSchemaProof(Autoprop(FSequent(And(A , B) :: Nil, Neg(Or(Neg(A), Neg(B))) :: Nil)))
//      //      Autoprop(FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil))
//      //      Autoprop(FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil))
//      //      Autoprop(FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil))
//
//      //      val f = Neg(Imp(Neg(Neg(A)), Neg(Neg(And(B,Neg(C))))))
//      //      println("NNF ("+printSchemaProof.formulaToString(f)+") = "+printSchemaProof.formulaToString(NNF(f)))
//    }
//  }
//}