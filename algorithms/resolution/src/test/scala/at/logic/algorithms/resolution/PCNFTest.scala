package at.logic.algorithms.resolution

import at.logic.language.fol._
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.parsing.readers.StringReader
import at.logic.calculi.lk._

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.calculi.resolution.base.FClause
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.quantificationRules.{ExistsRightRule, ForallLeftRule}


// we compare toStrings as proofs have only pointer equality. This needs to be changed by allowing syntaxEquals in graphs and vertices should
// have syntaxEquals as well

@RunWith(classOf[JUnitRunner])
class projectionsTest extends SpecificationWithJUnit {
  private class MyParser(str: String) extends StringReader(str) with SimpleFOLParser
  "PCNF" should {
    "create the projection of" in {
      val Pa = new MyParser("P(a)").getTerm.asInstanceOf[FOLFormula]
      val Qa = new MyParser("Q(a)").getTerm.asInstanceOf[FOLFormula]
      val nPa = Neg(Pa)
      val cPa = FClause(List(), List(Pa))
      "an atom Pa in the CNF(-s) where s is the sequent" in {
        val pPaPa = Axiom(List(Pa), List(Pa))
        "|- ¬Pa" in {
          val lkProof = NegRightRule(pPaPa, Pa)
          PCNF(FSequent(List(), List(nPa)), cPa).toString must beEqualTo (lkProof.toString)
        }
        "Pa |-" in {
          val lkProof = pPaPa
          PCNF(FSequent(List(Pa), List()), cPa).toString must beEqualTo (lkProof.toString)
        }
        /*"Pa ∨ Qa |- Qa" in {
          val PavQa = Or(Pa,Qa)
          val lkProof = OrLeftRule(Axiom(List(Pa),List(Pa)), Axiom(List(Qa),List(Qa)), Pa,Qa)
          PCNF(FSequent(List(PavQa), List(Qa)), cPa).toString must beEqualTo (lkProof.toString)
        }  */
        "|- ¬Pa ∨ Qa" in {
          val nPavQa = Or(nPa,Qa)
          val lkProof = OrRight1Rule(NegRightRule(Axiom(List(Pa),List(Pa)), Pa), nPa,Qa)
          PCNF(FSequent(List(), List(nPavQa)), cPa).toString must beEqualTo (lkProof.toString)
        }
        "|- Qa ∨ ¬Pa" in {
          val QavnPa = Or(Qa,nPa)
          val lkProof = OrRight2Rule(NegRightRule(Axiom(List(Pa),List(Pa)), Pa), Qa, nPa)
          PCNF(FSequent(List(), List(QavnPa)), cPa).toString must beEqualTo (lkProof.toString)
        }
        "Pa ∧ Qa |-" in {
          val PawQa = And(Pa,Qa)
          val lkProof = AndLeft1Rule(Axiom(List(Pa),List(Pa)), Pa, Qa)
          PCNF(FSequent(List(PawQa), List()), cPa).toString must beEqualTo (lkProof.toString)
        }
        "Qa ∧ Pa |-" in {
          val QawPa = And(Qa,Pa)
          val lkProof = AndLeft2Rule(Axiom(List(Pa),List(Pa)), Qa, Pa)
          PCNF(FSequent(List(QawPa), List()), cPa).toString must beEqualTo (lkProof.toString)
        }
        "Sa, Qa ∧ Pa |- Ra" in {
          val Sa = new MyParser("S(a)").getTerm.asInstanceOf[FOLFormula]
          val Ra = new MyParser("R(a)").getTerm.asInstanceOf[FOLFormula]
          val QawPa = And(Qa,Pa)
          val lkProof = WeakeningRightRule(WeakeningLeftRule(AndLeft2Rule(Axiom(List(Pa),List(Pa)), Qa, Pa),Sa),Ra)
          PCNF(FSequent(List(Sa,QawPa), List(Ra)), cPa).toString must beEqualTo (lkProof.toString)
        }
        /*"Qa |- ¬Pa ∧ Qa" in {
          val nPavQa = And(nPa,Qa)
          val lkProof = AndRightRule(NegRightRule(Axiom(List(Pa),List(Pa)),Pa), Axiom(List(Qa),List(Qa)), nPa,Qa)
          PCNF(FSequent(List(Qa), List(nPavQa)), cPa).toString must beEqualTo (lkProof.toString)
        }     */
        /*"add tests for imp right and left" in {

        } */
      }
      "an atom Px in the CNF(-f(s)) where s is the sequent" in {
        "∀xPx |-" in {
          val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
          val x = new MyParser("x").getTerm.asInstanceOf[FOLVar]
          val axPx = AllVar(x,Px)
          val lkProof = ForallLeftRule(Axiom(List(Px),List(Px)),Px, axPx, x)
          val cPx = FClause(List(), List(Px))
          PCNF(FSequent(List(axPx),List()),cPx).toString must beEqualTo (lkProof.toString)
        }
        "|- ∃xPx" in {
          val Px = new MyParser("P(x)").getTerm.asInstanceOf[FOLFormula]
          val x = new MyParser("x").getTerm.asInstanceOf[FOLVar]
          val exPx = ExVar(x,Px)
          val lkProof = ExistsRightRule(Axiom(List(Px),List(Px)),Px, exPx, x)
          val cPx = FClause(List(Px), List())
          PCNF(FSequent(List(),List(exPx)),cPx).toString must beEqualTo (lkProof.toString)
        }
      }
      /*"a negation ¬Pa in the CNF(-s) where s is the sequent" in {
        val Pa = new MyParser("P(a)").getTerm.asInstanceOf[FOLFormula]
        val nPa = Neg(Pa)
        "|- Pa" in {

        }
        "¬Pa |-" in {

        }
        "¬Pa ∨ Qa |- Qa" in {

        }
        "|- Pa ∨ Qa" in {

        }
        "|- Qa ∨ Pa" in {

        }
        "¬Pa ∧ Qa |-" in {

        }
        "Qa ∧ ¬Pa |-" in {

        }
        "Qa |- Pa ∧ Qa" in {

        }
        "∀x¬Px |-" in {

        }
        "|- ∃xPx" in {

        }
      }
      "a disjunction Pa ∨ Qa in the CNF(-s) where s is the sequent" in {
        val Pa = new MyParser("P(a)").getTerm.asInstanceOf[FOLFormula]
        "|- Pa" in {

        }
        "|- Qa" in {

        }
      }*/
    }
  }
}