package at.logic.transformations.ceres.ACNF

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.algorithms.hlk.HybridLatexParser
import java.io.File.separator
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 11/11/13
 * Time: 4:27 PM
 * To change this template use File | Settings | File Templates.
 */
/*
@RunWith(classOf[JUnitRunner])
class SubstituteProofTest extends SpecificationWithJUnit {
  "Proof substitution" should {
    val tokens = HybridLatexParser.parseFile("target" + separator + "substitutions.llk")
    val pdb = HybridLatexParser.createLKProof(tokens)
    val map  = Map[String, LKProof]() ++ pdb.proofs
    val x = HOLVar(StringSymbol("x"), Ti )
    val f = HOLConst(StringSymbol("f"), Ti -> Ti )
    val fa = Function(f, List(HOLConst(StringSymbol("a"), Ti)))

    val sub1 = Substitution(x,fa)

    "work on simple proofs (1)" in {
      println(map("P1").root)
      val p_ = SubstituteProof(map("P1"), sub1)
      println(p_.root)
      p_.root must beSyntacticMultisetEqual (map("P1").root)
    }

    "work on simple proofs (2)" in {
      val p_ = SubstituteProof(map("P2"), sub1)
      val fs = map("P2").root.toFSequent
      val fssub = FSequent(fs.antecedent map (x => sub1(x)),
                           fs.succedent map (x => sub1(x)))
      p_.root.toFSequent must beSyntacticFSequentEqual (fssub)
    }

    "work on simple proofs (3)" in {
      skipped("meh")
      val p_ = SubstituteProof(map("P3"), sub1)
      val fs = map("P3").root.toFSequent
      p_.root must beSyntacticMultisetEqual (map("P3").root)
      val fssub = FSequent(fs.antecedent map (x => sub1(x)),
        fs.succedent map (x => sub1(x)))
      p_.root.toFSequent must beSyntacticFSequentEqual (fssub)
    }


  }

}
*/