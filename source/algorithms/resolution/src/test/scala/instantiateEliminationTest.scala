package at.logic.algorithms.resolution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import at.logic.calculi.resolution.robinson.{Resolution, RobinsonResolutionProof, Paramodulation, InitialClause, Instance}
import at.logic.calculi.lk.base.{AuxiliaryFormulas, beSyntacticMultisetEqual}

@RunWith(classOf[JUnitRunner])
class instantiateEliminationTest extends SpecificationWithJUnit {

  object UNSproof {
    val v0 = FOLVar("v0")
    val v1 = FOLVar("v1")
    val v2 = FOLVar("v2")
    val a = FOLConst("a")
    val b = FOLConst("b")
    val c = FOLConst("c")

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

    val sub1 = Substitution(Map((v0,v2)))
    val sub2 = Substitution(Map((v1, add01)))
    val sub3 = Substitution(Map((v0,a), (v1,b),(v2,c)))
    val sub4 = Substitution(Map((v0,c), (v1,a),(v2,b)))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2a = Instance(p1,sub1 )
    val p2 = Instance(p2a,sub2 )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution())
    val p5 = Instance(p4, sub3)
    val p6 = InitialClause(c3::Nil, Nil)
    val p7 = Resolution(p5,p6,p5.root.succedent(0), p6.root.antecedent(0), sub3)
  }

  object UNSproof2 {
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

    val sub1 = Substitution(Map((v0,v2), (v1, add01)))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2 = Instance(p1,sub1 )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution())
  }

  "The instance elimination algorithm " should {
    "do instance merge " in {
      val proof = InstantiateElimination.imerge(UNSproof.p7, InstantiateElimination.emptyProofMap)._4
      proof.root must beSyntacticMultisetEqual(UNSproof.p7.root)
    }

    "do instance removal " in {
      val mproof = InstantiateElimination.imerge(UNSproof.p7, InstantiateElimination.emptyProofMap)._4
      mproof.root must beSyntacticMultisetEqual(UNSproof.p7.root)
      val rproof = InstantiateElimination.remove(mproof, InstantiateElimination.emptyVarSet, InstantiateElimination.emptyProofMap)._4
      rproof.root must beSyntacticMultisetEqual(UNSproof.p7.root)
    }
  }
}
