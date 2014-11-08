
package at.logic.algorithms.lk

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.{Sequent, FSequent}
import at.logic.calculi.lk._

@RunWith(classOf[JUnitRunner])
class RegularizationTest extends SpecificationWithJUnit {
  "Regularization" should {
    "apply correctly to a simple proof (1)" in {
      val x = HOLVar("x", Ti)
      val P = HOLConst("P", Ti -> To)
      val px = Atom(P, x::Nil )
      val s = FSequent( px::Nil, px::Nil )
      val ax1 = Axiom( px::Nil, px::Nil )
      val ax2 = Axiom( px::Nil, px::Nil )
      val proof = CutRule( ax1, ax2, ax1.root.succedent.head, ax2.root.antecedent.head )
      val p_s = regularize( proof )
      val s2 = p_s.root.toFSequent
      s2 must beEqualTo( s )
    }

    "apply to a simple proof (2)" in {
      skipped("Fix me. Should not depend so much on the names and the kind of renaming used")
      val List(a,b,x,y) = List("a","b","x","y") map ((x:String) => HOLVar(x, Ti))
      val List(k,l) = List("k","l") map ((x:String) => HOLConst(x, Ti))
      val P = HOLConst("P", Ti -> (Ti -> (Ti -> To)))
      val Pabk = Atom(P, List(a,b,k))
      val exPayk = ExVar(y, Atom(P, List(a,y,k)))
      val Q = HOLConst("Q", Ti -> (Ti -> (Ti -> (Ti -> To))))
      val Pxyk = Atom(Q, List(x,y,k,l))

      val l1 = Axiom( Pabk::Nil, Pabk::Nil )
      val l2 = ExistsRightRule(l1, l1.root.succedent(0), exPayk, b)
      val l3 = ExistsLeftRule(l2, l2.root.antecedent(0), exPayk, b)
      val l4 = WeakeningRightRule(l3, Pxyk)

      val r1 = Axiom( Pabk::Nil, Pabk::Nil )
      val r2 = ExistsRightRule(r1, r1.root.succedent(0), exPayk, b)
      val r3 = ExistsLeftRule(r2, r2.root.antecedent(0), exPayk, b)
      val r4 = WeakeningLeftRule(r3, Pxyk)

      val proof = CutRule(l4,r4,l4.root.succedent(1), r4.root.antecedent(1))
      val (rproof, blacklist, _) = regularize.recApply(proof)
      
      //val names = List("a","b","x","y","k","l","P","Q")
      val names = List(a, b, x, y, k, l, P, Q)
      for (name <- names)
        blacklist must contain (name)

      val regvars = regularize.variables(rproof)

      //our implementation always appends a number, so b will be removed from the original proof
      regvars must beEqualTo (blacklist  filterNot(_ == b))

      //the remaining symbols should be b_1,B_2 and the existential quantifier -- but since
      // the naming scheme may change, we only chek the size
      (blacklist.diff(names)).size must beEqualTo (3)

    }

    "apply to a simple proof (3)" in {
      skipped("Fix me. Should not depend so much on the names and the kind of renaming used")
      //this is similar to (2) but checks the universal quantifier and if there are no collisions between newly
      // generated vars and already existing ones
      val List(a,b,x,y) = List("a_1","a_2","x","y") map ((x:String) => HOLVar(x, Ti))
      val List(k,l) = List("k","l") map ((x:String) => HOLConst(x, Ti))
      val P = HOLConst("P", Ti -> (Ti -> (Ti -> To)))
      val Pabk = Atom(P, List(a,b,k))
      val exPayk = AllVar(y, Atom(P, List(a,y,k)))
      val Q = HOLConst("Q", Ti -> (Ti -> (Ti -> (Ti -> To))))
      val Pxyk = Atom(Q, List(x,y,k,l))

      val l1 = Axiom( Pabk::Nil, Pabk::Nil )
      val l2 = ForallLeftRule(l1, l1.root.antecedent(0), exPayk, b)
      val l3 = ForallRightRule(l2, l2.root.succedent(0), exPayk, b)
      val l4 = WeakeningRightRule(l3, Pxyk)

      val r1 = Axiom( Pabk::Nil, Pabk::Nil )
      val r2 = ForallLeftRule(r1, r1.root.antecedent(0), exPayk, b)
      val r3 = ForallRightRule(r2, r2.root.succedent(0), exPayk, b)
      val r4 = WeakeningLeftRule(r3, Pxyk)

      val proof = CutRule(l4,r4,l4.root.succedent(1), r4.root.antecedent(1))
      val (rproof, blacklist, _) = regularize.recApply(proof)

      //val names = List("a_1","a_2","x","y","k","l","P","Q")
      val names = List(a, b, x, y, k, l, P, Q)
      for (name <- names)
        blacklist must contain (name)

      val regvars = regularize.variables(rproof)

      //here a_1 will be taken, so the replacements of a_2 will be a_3 and a_4
      regvars must beEqualTo (blacklist filterNot (_ == b))

      //the remaining symbols should be b_1,B_2 and the existential quantifier -- but since
      // the naming scheme may change, we only chek the size
      (blacklist.diff(names)).size must beEqualTo (3)
    }

  }
}
