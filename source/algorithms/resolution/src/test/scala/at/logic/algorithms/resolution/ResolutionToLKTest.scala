package at.logic.algorithms.resolution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution.FClause
import at.logic.algorithms.lk.applySubstitution
import collection.immutable.Map.{Map1, Map2}

// we compare toStrings as proofs have only pointer equality. This needs to be changed by allowing syntaxEquals in graphs and vertices should
// have syntaxEquals as well

@RunWith(classOf[JUnitRunner])
class ResolutionToLKTest extends SpecificationWithJUnit {

  object UNSproof {
    val v0 = FOLVar("v0")
    val v1 = FOLVar("v1")
    val v2 = FOLVar("v2")

    val m01 = Function("multiply", v0::v1::Nil)
    val m10 = Function("multiply", v1::v0::Nil)
    val m02 = Function("multiply", v0::v2::Nil)
    val m12 = Function("multiply", v1::v2::Nil)
    val add01 = Function("add", v0::v1::Nil)
    val am02m12 = Function("add", m02::m12::Nil)
    val ma012 = Function("multiply", add01::v2::Nil)
    val m2a01 = Function("multiply", v2::add01::Nil)
    
    // =(multiply(v0, v1), multiply(v1, v0))
    val c1 = Equation(m01, m10)
    // =(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))
    val c2 = Equation(ma012, am02m12)
    // =(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))
    val c3 = Equation(m2a01, am02m12)

    val sub = Substitution(Map((v0,v2), (v1, add01)))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2 = Instance(p1,sub )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution())

  }
  object UNSproofFreshvars {
    val v0 = FOLVar("v0")
    val v0u = FOLVar("v0_")
    val v1 = FOLVar("v1")
    val v1u = FOLVar("v1_")
    val v2 = FOLVar("v2")

    val m01u = Function("multiply", v0u::v1u::Nil)
    val m10u = Function("multiply", v1u::v0u::Nil)
    val m02 = Function("multiply", v0::v2::Nil)
    val m12 = Function("multiply", v1::v2::Nil)
    val add01 = Function("add", v0::v1::Nil)
    val am02m12 = Function("add", m02::m12::Nil)
    val ma012 = Function("multiply", add01::v2::Nil)
    val m2a01 = Function("multiply", v2::add01::Nil)
   
    // =(multiply(v0_, v1_), multiply(v1_, v0_))
    val c1 = Equation(m01u, m10u)
    // =(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))
    val c2 = Equation(ma012, am02m12)
    // =(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))
    val c3 = Equation(m2a01, am02m12)  

    val sub = Substitution(Map((v0,v2), (v1, add01)))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2 = Instance(p1,sub )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution())

  }
  object UNSproofVariant {
    val v0 = FOLVar("v0")
    val v0u = FOLVar("v0_")
    val v1 = FOLVar("v1")
    val v1u = FOLVar("v1_")
    val v2 = FOLVar("v2")

    val m01 = Function("multiply", v0::v1::Nil)
    val m10 = Function("multiply", v1::v0::Nil)
    val m02 = Function("multiply", v0::v2::Nil)
    val m12 = Function("multiply", v1::v2::Nil)
    val add01 = Function("add", v0::v1::Nil)
    val am02m12 = Function("add", m02::m12::Nil)
    val ma012 = Function("multiply", add01::v2::Nil)
    val m2a01 = Function("multiply", v2::add01::Nil)
   
    // =(multiply(v0, v1), multiply(v1, v0))
    val c1 = Equation(m01, m10)
    // =(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))
    val c2 = Equation(ma012, am02m12)
    // =(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))
    val c3 = Equation(m2a01, am02m12)     

    val sub1 = Substitution(Map((v0,v0u), (v1, v1u)))
    val sub2 = Substitution(Map((v0u,v2), (v1u, add01)))

    val p1 = InitialClause(Nil, c1::Nil)
    val p1_ = Variant(p1,sub1 )
    val p2 = Instance(p1,sub2 )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution())

  }

  "RobinsonToLK" should {
    "transform the following resolution proof into an LK proof of the empty sequent" in {
      "containing only an initial clause" in {
        val Pa = Atom("P", FOLConst("a")::Nil)
        val resProof = InitialClause(Pa :: List.empty, Pa :: List.empty)
        val lkProof = Axiom(Pa :: List.empty, Pa :: List.empty)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a factorized clause" in {
        val a = FOLConst("a")
        val x = FOLVar("x")
        val y = FOLVar("y")
        val fa = Function("f", a::Nil)
        val fy = Function("f", y::Nil)
        val Pfa = Atom("P", fa::Nil)
        val Pfy = Atom("P", fy::Nil)
        val Px = Atom("P", x::Nil)

        val p1 = InitialClause(Pfa :: Px :: Pfy :: List.empty, List.empty)
        val resProof = Factor(p1, p1.root.negative(1), List(p1.root.negative(0), p1.root.negative(2)), Substitution(new Map2(x, fa, y, a)))

        val l1 = Axiom(List(Pfa, Pfa, Pfa), List())
        val l2 = ContractionLeftRule(l1, l1.root.antecedent(1), l1.root.antecedent(0))
        val lkProof = ContractionLeftRule(l2, l2.root.antecedent(0), l2.root.antecedent(1))
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a variant clause" in {
        val x = FOLVar("x")
        val y = FOLVar("y")
        val Px = Atom("P", x::Nil)
        val Py = Atom("P", y::Nil)

        val p1 = InitialClause(List(Px), List.empty)
        val resProof = Variant(p1, Substitution(new Map1(x, y)))

        val lkProof = Axiom(List(Py), List())
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a resolution clause" in {
        val x = FOLVar("x")
        val a = FOLConst("a")
        val fa = Function("f", a::Nil)
        val ffa = Function("f", fa::Nil)
        val fx = Function("f", x::Nil)
        val Px = Atom("P", x::Nil)
        val Pfx = Atom("P", fx::Nil)
        val Pfa = Atom("P", fa::Nil)
        val Pffa = Atom("P", ffa::Nil)

        val p1 = InitialClause(List(Px), List(Pfx))
        val p2 = InitialClause(List(Pffa), List(Pfa))
        val resProof = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(0), Substitution(new Map1(x, fa)))

        val l1 = Axiom(List(Pfa), List(Pffa))
        val l2 = Axiom(List(Pffa), List(Pfa))
        val lkProof = CutRule(l2, l1, l2.root.succedent(0), l1.root.antecedent(0))
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a paramodulation clause for rule 1" in {
        val a = FOLConst("a")
        val b = FOLConst("b")
        val x = FOLVar("x")
        val exb = Equation(x, b)
        val eab = Equation(a, b)
        val Pfa = Atom("P", Function("f", a::Nil)::Nil)
        val Pfb = Atom("P", Function("f", b::Nil)::Nil)

        val p1 = InitialClause(List(), List(exb))
        val p2 = InitialClause(List(Pfa), List())
        val resProof = Paramodulation(p1, p2, p1.root.positive(0), p2.root.negative(0), Pfb, Substitution(new Map1(x, a)))

        val l1 = Axiom(List(), List(eab))
        val l2 = Axiom(List(Pfa), List())
        val lkProof = EquationLeft1Rule(l1, l2, l1.root.succedent(0), l2.root.antecedent(0), Pfb)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a paramodulation clause for rule 2" in {
        val a = FOLConst("a")
        val b = FOLConst("b")
        val x = FOLVar("x")
        val ebx = Equation(b, x)
        val eba = Equation(b, a)
        val Pfa = Atom("P", Function("f", a::Nil)::Nil)
        val Pfb = Atom("P", Function("f", b::Nil)::Nil)

        val p1 = InitialClause(List(), List(ebx))
        val p2 = InitialClause(List(Pfa), List())
        val resProof = Paramodulation(p1, p2, p1.root.positive(0), p2.root.negative(0), Pfb, Substitution(new Map1(x, a)))

        val l1 = Axiom(List(), List(eba))
        val l2 = Axiom(List(Pfa), List())
        val lkProof = EquationLeft2Rule(l1, l2, l1.root.succedent(0), l2.root.antecedent(0), Pfb)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
    }
    "transform a resolution proof into an LK proof of the weakly quantified sequent" in {
      "∀xPx |-  Pa" in {
        val x = FOLVar("x")
        val y = FOLVar("y")
        val a = FOLConst("a")
        val Px = Atom("P", x::Nil)
        val Pa = Atom("P", a::Nil)
        val f1 = AllVar(x, Px)

        val seq = FSequent(List(f1),List(Pa))
        val p1 = InitialClause(List(), List(Px))
        val p2 = InitialClause(List(Pa), List())
        val v1 = Variant(p1, Substitution(new Map1(x, y)))
        val resProof = Resolution(v1,p2,v1.root.positive(0), p2.root.negative(0), Substitution(new Map1(y, a)))
        RobinsonToLK(resProof, seq).root.toFSequent.toString must beEqualTo(FSequent(List(f1),List(Pa)).toString)
      }
      "transform the original subproof of the UNS example" in {
        val r = RobinsonToLK(UNSproof.p4).root
        r.antecedent must beEmpty
        r.succedent.size mustEqual(1)
        r.succedent(0).formula mustEqual(UNSproof.c3)
      }
      "transform the subproof of the UNS example with unique variables" in {
        skipped("does not work! fix!")
        val r = RobinsonToLK(UNSproofFreshvars.p4).root
        r.antecedent must beEmpty
        r.succedent.size mustEqual(1)
        r.succedent(0).formula mustEqual(UNSproofFreshvars.c3)
      }
      "transform the subproof of the UNS example with introduced variant" in {
        skipped("does not work! fix!")
        val r = RobinsonToLK(UNSproofVariant.p4).root
        r.antecedent must beEmpty
        r.succedent.size mustEqual(1)
        r.succedent(0).formula mustEqual(UNSproofVariant.c3)
      }
    }
  }
}
