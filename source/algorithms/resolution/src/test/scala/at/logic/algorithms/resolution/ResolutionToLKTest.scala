package at.logic.algorithms.resolution

import at.logic.calculi.lk.equationalRules.{EquationLeft2Rule, EquationLeft1Rule}
import at.logic.language.fol._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{Var, LambdaExpression}
import collection.immutable.Map.{Map1, Map2}
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution.instance.Instance
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base.FClause
import at.logic.algorithms.lk.applySubstitution

// we compare toStrings as proofs have only pointer equality. This needs to be changed by allowing syntaxEquals in graphs and vertices should
// have syntaxEquals as well

@RunWith(classOf[JUnitRunner])
class ResolutionToLKTest extends SpecificationWithJUnit {
  private class MyParser(str: String) extends StringReader(str) with SimpleFOLParser

  object UNSproof {
    def fparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLFormula]
    def tparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLTerm]
    val c1 = fparse("=(multiply(v0, v1), multiply(v1, v0))")
    val c2 = fparse("=(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))")
    val c3 = fparse("=(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))")
    val List(v0,v1,v2) = List("v0","v1","v2").map(tparse(_).asInstanceOf[FOLVar])
    val addv0v1 = tparse("add(v0,v1)")
    val sub = Substitution[FOLExpression]((v0,v2), (v1, addv0v1))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2 = Instance(p1,sub )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution[FOLExpression]())
    //val p5 = Paramodulation(p1,p3, p1.root.succedent(0), p3.root.succedent(0), c3, sub)

  }
  object UNSproofFreshvars {
    def fparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLFormula]
    def tparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLTerm]
    val c1 = fparse("=(multiply(v0_, v1_), multiply(v1_, v0_))")
    val c2 = fparse("=(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))")
    val c3 = fparse("=(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))")
    val List(v0,v1,v2) = List("v0_","v1_","v2").map(tparse(_).asInstanceOf[FOLVar])
    val addv0v1 = tparse("add(v0,v1)")
    val sub = Substitution[FOLExpression]((v0,v2), (v1, addv0v1))

    val p1 = InitialClause(Nil, c1::Nil)
    val p2 = Instance(p1,sub )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution[FOLExpression]())

  }
  object UNSproofVariant {
    def fparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLFormula]
    def tparse(s:String) = new MyParser(s).getTerm.asInstanceOf[FOLTerm]
    val c1 = fparse("=(multiply(v0, v1), multiply(v1, v0))")
    val c2 = fparse("=(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))")
    val c3 = fparse("=(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))")
    val List(v0,v1,v0_, v1_, v2) = List("v0","v1","v0_","v1_","v2").map(tparse(_).asInstanceOf[FOLVar])
    val addv0v1 = tparse("add(v0,v1)")
    val sub1 = Substitution[FOLExpression]((v0,v0_), (v1, v1_))
    val sub2 = Substitution[FOLExpression]((v0_,v2), (v1_, addv0v1))

    val p1 = InitialClause(Nil, c1::Nil)
    val p1_ = Variant(p1,sub1 )
    val p2 = Instance(p1,sub2 )
    val p3 = InitialClause(Nil, c2::Nil)
    val p4 = Paramodulation(p2, p3, p2.root.succedent(0), p3.root.succedent(0), c3, Substitution[FOLExpression]())

  }

  "RobinsonToLK" should {
    "transform the following resolution proof into an LK proof of the empty sequent" in {
      "containing only an initial clause" in {
        val Pa = new MyParser("P(a)").getTerm.asInstanceOf[FOLFormula]
        val resProof = InitialClause(Pa :: List.empty, Pa :: List.empty)
        val lkProof = Axiom(Pa :: List.empty, Pa :: List.empty)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a factorized clause" in {
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
        val Pfy = new MyParser("P(f(y))").getTerm.asInstanceOf[FOLFormula]
        val fa = new MyParser("f(a)").getTerm
        val a = new MyParser("a").getTerm
        val x = new MyParser("x").getTerm
        val y = new MyParser("y").getTerm

        val p1 = InitialClause(Pfa :: Px :: Pfy :: List.empty, List.empty)
        val resProof = Factor(p1, p1.root.negative(1), List(p1.root.negative(0), p1.root.negative(2)), Substitution(new Map2(x, fa, y, a).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(Pfa, Pfa, Pfa), List())
        val l2 = ContractionLeftRule(l1, l1.root.antecedent(1), l1.root.antecedent(0))
        val lkProof = ContractionLeftRule(l2, l2.root.antecedent(0), l2.root.antecedent(1))
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a variant clause" in {
        val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
        val Py = new MyParser("P(y)").getTerm.asInstanceOf[FOLFormula]
        val x = new MyParser("x").getTerm
        val y = new MyParser("y").getTerm

        val p1 = InitialClause(List(Px), List.empty)
        val resProof = Variant(p1, Substitution(new Map1(x, y).asInstanceOf[Map[Var, FOLExpression]]))

        val lkProof = Axiom(List(Py), List())
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a resolution clause" in {
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
        val Pfx = new MyParser("P(f(x))").getTerm.asInstanceOf[FOLFormula]
        val Pffa = new MyParser("P(f(f(a)))").getTerm.asInstanceOf[FOLFormula]
        val fa = new MyParser("f(a)").getTerm
        val x = new MyParser("x").getTerm

        val p1 = InitialClause(List(Px), List(Pfx))
        val p2 = InitialClause(List(Pffa), List(Pfa))
        val resProof = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(0), Substitution(new Map1(x, fa).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(Pfa), List(Pffa))
        val l2 = Axiom(List(Pffa), List(Pfa))
        val lkProof = CutRule(l2, l1, l2.root.succedent(0), l1.root.antecedent(0))
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a paramodulation clause for rule 1" in {
        val exb = new MyParser("=(x,b)").getTerm.asInstanceOf[FOLFormula]
        val eab = new MyParser("=(a,b)").getTerm.asInstanceOf[FOLFormula]
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Pfb = new MyParser("P(f(b))").getTerm.asInstanceOf[FOLFormula]
        val a = new MyParser("a").getTerm
        val x = new MyParser("x").getTerm

        val p1 = InitialClause(List(), List(exb))
        val p2 = InitialClause(List(Pfa), List())
        val resProof = Paramodulation(p1, p2, p1.root.positive(0), p2.root.negative(0), Pfb, Substitution(new Map1(x, a).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(), List(eab))
        val l2 = Axiom(List(Pfa), List())
        val lkProof = EquationLeft1Rule(l1, l2, l1.root.succedent(0), l2.root.antecedent(0), Pfb)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a paramodulation clause for rule 2" in {
        val ebx = new MyParser("=(b,x)").getTerm.asInstanceOf[FOLFormula]
        val eba = new MyParser("=(b,a)").getTerm.asInstanceOf[FOLFormula]
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Pfb = new MyParser("P(f(b))").getTerm.asInstanceOf[FOLFormula]
        val a = new MyParser("a").getTerm
        val x = new MyParser("x").getTerm

        val p1 = InitialClause(List(), List(ebx))
        val p2 = InitialClause(List(Pfa), List())
        val resProof = Paramodulation(p1, p2, p1.root.positive(0), p2.root.negative(0), Pfb, Substitution(new Map1(x, a).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(), List(eba))
        val l2 = Axiom(List(Pfa), List())
        val lkProof = EquationLeft2Rule(l1, l2, l1.root.succedent(0), l2.root.antecedent(0), Pfb)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
    }
    "transform a resolution proof into an LK proof of the weakly quantified sequent" in {
      "∀xPx |-  Pa" in {
        val f1 = new MyParser("Forall x P(x)").getTerm.asInstanceOf[FOLFormula]
        val Pa = new MyParser("P(a)").getTerm.asInstanceOf[FOLFormula]
        val seq = FSequent(List(f1),List(Pa))
        val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
        val x = new MyParser("x").getTerm
        val y = new MyParser("y").getTerm
        val a = new MyParser("a").getTerm
        val p1 = InitialClause(List(), List(Px))
        val p2 = InitialClause(List(Pa), List())
        val v1 = Variant(p1, Substitution(new Map1(x, y).asInstanceOf[Map[Var, FOLExpression]]))
        val resProof = Resolution(v1,p2,v1.root.positive(0), p2.root.negative(0), Substitution(new Map1(y, a).asInstanceOf[Map[Var, FOLExpression]]))
        /*val lkProof1 = applySubstitution(PCNF(FSequent(List(f1),List()), cls1), Substitution(new Map1(x, a).asInstanceOf[Map[Var, FOLExpression]]))._1
        val lkProof2 = PCNF(FSequent(List(),List(Pa)), cls2)
        val lkProof = CutRule(lkProof1,lkProof2, Pa) */
        RobinsonToLK(resProof, seq).root.toFSequent.toString must beEqualTo(FSequent(List(f1),List(Pa)).toString)
      }
      "transform the original subproof of the UNS example" in {
	skipped("does not work")
        val r = RobinsonToLK(UNSproof.p4).root
        r.antecedent must beEmpty
        r.succedent.size mustEqual(1)
        r.succedent(0).formula mustEqual(UNSproof.c3)
      }
      "transform the subproof of the UNS example with unique variables" in {
        val r = RobinsonToLK(UNSproofFreshvars.p4).root
        r.antecedent must beEmpty
        r.succedent.size mustEqual(1)
        r.succedent(0).formula mustEqual(UNSproofFreshvars.c3)
      }
      "transform the subproof of the UNS example with introduced variant" in {
        val r = RobinsonToLK(UNSproofVariant.p4).root
        r.antecedent must beEmpty
        r.succedent.size mustEqual(1)
        r.succedent(0).formula mustEqual(UNSproofVariant.c3)
      }
      /*"containing a factorized clause" in {
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
        val Pfy = new MyParser("P(f(y))").getTerm.asInstanceOf[FOLFormula]
        val fa = new MyParser("f(a)").getTerm
        val a = new MyParser("a").getTerm
        val x = new MyParser("x").getTerm
        val y = new MyParser("y").getTerm

        val p1 = InitialClause(Pfa :: Px :: Pfy :: List.empty, List.empty)
        val resProof = Factor(p1, p1.root.negative(1), List(p1.root.negative(0), p1.root.negative(2)), Substitution(new Map2(x, fa, y, a).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(Pfa, Pfa, Pfa), List())
        val l2 = ContractionLeftRule(l1, l1.root.antecedent(1), l1.root.antecedent(0))
        val lkProof = ContractionLeftRule(l2, l2.root.antecedent(0), l2.root.antecedent(1))
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a variant clause" in {
        val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
        val Py = new MyParser("P(y)").getTerm.asInstanceOf[FOLFormula]
        val x = new MyParser("x").getTerm
        val y = new MyParser("y").getTerm

        val p1 = InitialClause(List(Px), List.empty)
        val resProof = Variant(p1, Substitution(new Map1(x, y).asInstanceOf[Map[Var, FOLExpression]]))

        val lkProof = Axiom(List(Py), List())
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a resolution clause" in {
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
        val Pfx = new MyParser("P(f(x))").getTerm.asInstanceOf[FOLFormula]
        val Pffa = new MyParser("P(f(f(a)))").getTerm.asInstanceOf[FOLFormula]
        val fa = new MyParser("f(a)").getTerm
        val x = new MyParser("x").getTerm

        val p1 = InitialClause(List(Px), List(Pfx))
        val p2 = InitialClause(List(Pffa), List(Pfa))
        val resProof = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(0), Substitution(new Map1(x, fa).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(Pfa), List(Pffa))
        val l2 = Axiom(List(Pffa), List(Pfa))
        val lkProof = CutRule(l2, l1, l2.root.succedent(0), l1.root.antecedent(0))
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a paramodulation clause for rule 1" in {
        val exb = new MyParser("=(x,b)").getTerm.asInstanceOf[FOLFormula]
        val eab = new MyParser("=(a,b)").getTerm.asInstanceOf[FOLFormula]
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Pfb = new MyParser("P(f(b))").getTerm.asInstanceOf[FOLFormula]
        val a = new MyParser("a").getTerm
        val x = new MyParser("x").getTerm

        val p1 = InitialClause(List(), List(exb))
        val p2 = InitialClause(List(Pfa), List())
        val resProof = Paramodulation(p1, p2, p1.root.positive(0), p2.root.negative(0), Pfb, Substitution(new Map1(x, a).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(), List(eab))
        val l2 = Axiom(List(Pfa), List())
        val lkProof = EquationLeft1Rule(l1, l2, l1.root.succedent(0), l2.root.antecedent(0), Pfb)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      }
      "containing a paramodulation clause for rule 2" in {
        val ebx = new MyParser("=(b,x)").getTerm.asInstanceOf[FOLFormula]
        val eba = new MyParser("=(b,a)").getTerm.asInstanceOf[FOLFormula]
        val Pfa = new MyParser("P(f(a))").getTerm.asInstanceOf[FOLFormula]
        val Pfb = new MyParser("P(f(b))").getTerm.asInstanceOf[FOLFormula]
        val a = new MyParser("a").getTerm
        val x = new MyParser("x").getTerm

        val p1 = InitialClause(List(), List(ebx))
        val p2 = InitialClause(List(Pfa), List())
        val resProof = Paramodulation(p1, p2, p1.root.positive(0), p2.root.negative(0), Pfb, Substitution(new Map1(x, a).asInstanceOf[Map[Var, FOLExpression]]))

        val l1 = Axiom(List(), List(eba))
        val l2 = Axiom(List(Pfa), List())
        val lkProof = EquationLeft2Rule(l1, l2, l1.root.succedent(0), l2.root.antecedent(0), Pfb)
        RobinsonToLK(resProof).toString must beEqualTo(lkProof.toString)
      } */
    }
  }
}
