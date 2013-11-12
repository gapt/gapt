package at.logic.transformations.ceres.ACNF

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.algorithms.hlk.HybridLatexParser
import java.io.File.separator
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.hol._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.Ti
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.lk.lkSpecs.{beSyntacticMultisetEqual, beSyntacticFSequentEqual}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.Ti
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.lk.lkSpecs.beSyntacticMultisetEqual
import at.logic.language.lambda.typedLambdaCalculus.Var

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 11/11/13
 * Time: 4:27 PM
 * To change this template use File | Settings | File Templates.
 */
@RunWith(classOf[JUnitRunner])
class SubstituteProofTest extends SpecificationWithJUnit {
  "Proof substitution" should {
    val tokens = HybridLatexParser.parseFile("target" + separator + "test-classes" + separator + "substitutions.llk")
    val pdb = HybridLatexParser.createLKProof(tokens)
    val map  = Map[String, LKProof]() ++ pdb.proofs
    val x = HOLVar(VariableStringSymbol("x"), Ti() )
    val fa = Function(ConstantStringSymbol("f"), List(HOLConst(ConstantStringSymbol("a"), Ti())), Ti())

    val sub1 = Substitution[HOLExpression](List((x.asInstanceOf[Var],fa)))

    "work on simple proofs (1)" in {
      //skipped("meh")
      println(map("P1").root)
      val p_ = SubstituteProof(map("P1"), sub1)
      println(p_.root)
      p_.root must beSyntacticMultisetEqual (map("P1").root)
    }

    "work on simple proofs (2)" in {
      val p_ = SubstituteProof(map("P2"), sub1)
      val fs = map("P2").root.toFSequent
      val fssub = FSequent(fs.antecedent map (x => sub1(x).asInstanceOf[HOLFormula]),
                           fs.succedent map (x => sub1(x).asInstanceOf[HOLFormula]))
      p_.root.toFSequent() must beSyntacticFSequentEqual (fssub)
    }

    "work on simple proofs (3)" in {
      skipped("meh")
      val p_ = SubstituteProof(map("P3"), sub1)
      val fs = map("P3").root.toFSequent
      p_.root must beSyntacticMultisetEqual (map("P3").root)
      val fssub = FSequent(fs.antecedent map (x => sub1(x).asInstanceOf[HOLFormula]),
        fs.succedent map (x => sub1(x).asInstanceOf[HOLFormula]))
      p_.root.toFSequent() must beSyntacticFSequentEqual (fssub)
    }


  }

}
