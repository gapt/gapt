package at.logic.gapt.proofs.algorithms.ceres.ACNF

import org.specs2.mutable._
import at.logic.gapt.formats.llk.HybridLatexParser
import java.io.File.separator
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lkOld.base._

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 11/11/13
 * Time: 4:27 PM
 * To change this template use File | Settings | File Templates.
 */
/*
class SubstituteProofTest extends Specification {
  "Proof substitution" should {
    val tokens = HybridLatexParser.parseFile("target" + separator + "substitutions.llk")
    val pdb = HybridLatexParser.createLKProof(tokens)
    val map  = Map[String, LKProof]() ++ pdb.proofs
    val x = Var(StringSymbol("x"), Ti )
    val f = Const(StringSymbol("f"), Ti -> Ti )
    val fa = Function(f, List(Const(StringSymbol("a"), Ti)))

    val sub1 = Substitution(x,fa)

    "work on simple proofs (1)" in {
      println(map("P1").root)
      val p_ = SubstituteProof(map("P1"), sub1)
      println(p_.root)
      p_.root must beSyntacticMultisetEqual (map("P1").root)
    }

    "work on simple proofs (2)" in {
      val p_ = SubstituteProof(map("P2"), sub1)
      val fs = map("P2").root.toHOLSequent
      val fssub = FSequent(fs.antecedent map (x => sub1(x)),
                           fs.succedent map (x => sub1(x)))
      p_.root.toHOLSequent must beSyntacticFSequentEqual (fssub)
    }

    "work on simple proofs (3)" in {
      skipped("meh")
      val p_ = SubstituteProof(map("P3"), sub1)
      val fs = map("P3").root.toHOLSequent
      p_.root must beSyntacticMultisetEqual (map("P3").root)
      val fssub = FSequent(fs.antecedent map (x => sub1(x)),
        fs.succedent map (x => sub1(x)))
      p_.root.toHOLSequent must beSyntacticFSequentEqual (fssub)
    }


  }

}
*/
