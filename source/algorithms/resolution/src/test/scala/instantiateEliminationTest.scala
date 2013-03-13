package at.logic.algorithms.resolution
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.language.fol.{FOLExpression, FOLVar, FOLTerm, FOLFormula}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.resolution.robinson.{Resolution, RobinsonResolutionProof, Paramodulation, InitialClause}
import at.logic.calculi.resolution.instance.Instance
import at.logic.calculi.lk.lkSpecs.beSyntacticMultisetEqual
import at.logic.calculi.lk.base.AuxiliaryFormulas

@RunWith(classOf[JUnitRunner])
class instantiateEliminationTest extends SpecificationWithJUnit {
  private class MyParser(str: String) extends StringReader(str) with SimpleFOLParser

  object UNSproof {
    def fparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLFormula]
    def tparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLTerm]
    val c1 = fparse("=(multiply(v0, v1), multiply(v1, v0))")
    val c2 = fparse("=(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))")
    val c3 = fparse("=(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))")
    val List(v0,v1,v2) = List("v0","v1","v2").map(tparse(_).asInstanceOf[FOLVar])
    val addv0v1 = tparse("add(v0,v1)")
    val List(a,b,c) = List("a","b","c") map tparse

    val sub1 = Substitution[FOLExpression]((v0,v2))
    val sub2 = Substitution[FOLExpression]((v1, addv0v1))
    val sub3 = Substitution[FOLExpression]((v0,a), (v1,b),(v2,c))
    val sub4 = Substitution[FOLExpression]((v0,c), (v1,a),(v2,b))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2a = Instance(p1,sub1 )
    val p2 = Instance(p2a,sub2 )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution[FOLExpression]())
    val p5 = Instance(p4, sub3)
    val p6 = InitialClause(c3::Nil, Nil)

    //println(p5.root.occurrences)
    //println(p6.root.occurrences)
    val p7 = Resolution(p5,p6,p5.root.succedent(0), p6.root.antecedent(0), sub3)

    //val p5 = Paramodulation(p1,p3, p1.root.succedent(0), p3.root.succedent(0), c3, sub)

  }

  object UNSproof2 {
    def fparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLFormula]
    def tparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLTerm]
    val c1 = fparse("=(multiply(v0, v1), multiply(v1, v0))")
    val c2 = fparse("=(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))")
    val c3 = fparse("=(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))")
    val List(v0,v1,v2) = List("v0","v1","v2").map(tparse(_).asInstanceOf[FOLVar])
    val addv0v1 = tparse("add(v0,v1)")
    val sub1 = Substitution[FOLExpression]((v0,v2), (v1, addv0v1))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2 = Instance(p1,sub1 )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution[FOLExpression]())
    //val p5 = Paramodulation(p1,p3, p1.root.succedent(0), p3.root.succedent(0), c3, sub)

  }


  "The instance elimination algorithm " should {
    "do instance merge " in {
      val proof = InstantiateElimination.imerge(UNSproof.p7, InstantiateElimination.emptyProofMap)._4
      proof.root must beSyntacticMultisetEqual(UNSproof.p7.root)

    }

    "do instance removal " in {
      val mproof = InstantiateElimination.imerge(UNSproof.p7, InstantiateElimination.emptyProofMap)._4
      mproof.root must beSyntacticMultisetEqual(UNSproof.p7.root)
      /*
      mproof.nodes.asInstanceOf[Set[RobinsonResolutionProof]] map (x => {
        println("node:        "+x.rule)
        println("occurrences: "+x.root.occurrences )
        if (x.isInstanceOf[RobinsonResolutionProof with AuxiliaryFormulas])
          println("auxiliars:   "+x.asInstanceOf[RobinsonResolutionProof with AuxiliaryFormulas].aux)
        println()
      })
      */

      //println("===================================================================================")
      val rproof = InstantiateElimination.remove(mproof, InstantiateElimination.emptyVarSet, InstantiateElimination.emptyProofMap)._4
      rproof.root must beSyntacticMultisetEqual(UNSproof.p7.root)


    }


  }

}
