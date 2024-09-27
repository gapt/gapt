package gapt.proofs.resolution

import gapt.examples.{BussTautology, CountingEquivalence}
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.{naive, thresholds}
import gapt.expr.subst.FOLSubstitution
import gapt.expr.subst.Substitution
import gapt.proofs.lk._
import gapt.proofs._
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.provers.escargot.Escargot
import gapt.provers.prover9.Prover9
import gapt.utils.SatMatchers
import org.specs2.mutable._

class ResolutionToLKTest extends Specification with SequentMatchers with SatMatchers {

  object UNSproof {
    val c1 = hof"multiply v0 v1 = multiply v1 v0"
    val c2 = hof"multiply (add v0 v1) v2 = add (multiply v0 v2) (multiply v1 v2)"
    val c3 = hof"multiply v2 (add v0 v1) = add (multiply v0 v2) (multiply v1 v2)"

    val sub = Substitution(hov"v0" -> le"v2", hov"v1" -> le"add v0 v1")

    val p1 = Input(Clause() :+ c1)
    val p2 = Subst(p1, sub)
    val p3 = Input(Clause() :+ c2)
    val p4 = Paramod.withMain(p2, Suc(0), p3, Suc(0), c3)
  }

  "ResolutionToLKProof" should {
    "containing only an initial clause" in {
      val Pa = FOLAtom("P", FOLConst("a") :: Nil)
      ResolutionToLKProof(Taut(Pa)) must_== LogicalAxiom(Pa)
    }
    "transform a resolution proof into an LK proof of the weakly quantified sequent" in {
      "∀xPx |-  Pa" in {
        val x = FOLVar("x")
        val y = FOLVar("y")
        val a = FOLConst("a")
        val Px = FOLAtom("P", x :: Nil)
        val Pa = FOLAtom("P", a :: Nil)
        val f1 = All(x, Px)

        val seq = HOLSequent(List(f1), List(Pa))
        val p1 = Input(Clause() :+ Px)
        val p2 = Input(Pa +: Clause())
        val v1 = Subst(p1, FOLSubstitution(x -> y))
        val resProof = Resolution(Subst(v1, FOLSubstitution(y -> a)), Suc(0), p2, Ant(0))
        ResolutionToLKProof(fixDerivation(resProof, seq)).endSequent must_== (f1 +: Sequent() :+ Pa)
      }
      "transform the original subproof of the UNS example" in {
        ResolutionToLKProof.asDerivation(UNSproof.p4).endSequent must_== (Sequent() :+ UNSproof.c3)
      }
    }

    "transform rewriting at multiple positions" in {
      val proof = ResolutionToLKProof.asDerivation(
        Paramod(
          Input(Clause() :+ hoa"a = b"),
          Suc(0),
          true,
          Input(Clause() :+ hoa"p a a"),
          Suc(0),
          le"^x p x x: o"
        )
      )
      proof.endSequent must beMultiSetEqual(Sequent() :+ hoa"p b b")
    }

    "duplicate bound variables" in {
      val Seq(p, q) = Seq("p", "q") map { FOLAtomConst(_, 1) }
      val Seq(c, d) = Seq("c", "d") map { FOLConst(_) }
      val x = FOLVar("x")

      val endSequent = Sequent() :+ ((All(x, p(x)) | All(x, q(x))) --> (p(c) | q(d)))

      val Some(ref) = Escargot getResolutionProof endSequent: @unchecked
      val expansion = ResolutionToExpansionProof(ref)
      expansion.shallow must_== endSequent
      expansion.deep must beValidSequent
    }

    "structural cnf with definitions" in {
      val Some(p) = Escargot getLKProof BussTautology(3): @unchecked
      p.conclusion must beMultiSetEqual(BussTautology(3))
    }
    "structural cnf 2" in {
      val as = 0 to 3 map { i => FOLAtom(s"a$i") }
      val endSequent = thresholds.exactly.oneOf(as) +: Sequent() :+ naive.exactly.oneOf(as)
      val Some(p) = Escargot getLKProof endSequent: @unchecked
      p.conclusion must beMultiSetEqual(endSequent)
    }

    "counting example" in {
      val Some(p) = Escargot.getLKProof(CountingEquivalence(1)): @unchecked
      p.conclusion must_== (Sequent() :+ CountingEquivalence(1))
    }
  }
}
