/*
 * equationalRules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.mutable.HashMap
import base._
import at.logic.utils.traits.Occurrence

package equationalRules {

  // Definition rules
  case object EquationLeft1RuleType extends BinaryRuleTypeA
  case object EquationLeft2RuleType extends BinaryRuleTypeA
  case object EquationRight1RuleType extends BinaryRuleTypeA
  case object EquationRight2RuleType extends BinaryRuleTypeA

  //TODO: perhaps there is a better place for this
  object EquationVerifier {
    //results
    abstract class ReplacementResult;
    case object Equal extends ReplacementResult;
    case object Different extends ReplacementResult;
    case class EqualModuloEquality(path : List[Int]) extends ReplacementResult;

    def apply(s : LambdaExpression, t : LambdaExpression, e1 : LambdaExpression, e2 : LambdaExpression) = checkReplacement(s,t,e1,e2)
    //this is a convenience method, apart from that everything is general
    def apply(eq : HOLFormula, e1 : HOLFormula, e2:HOLFormula) : Option[List[Int]] = {
      eq match {
        case Equation(s,t) => apply(s,t,e1,e2) match {
          case EqualModuloEquality(path) => Some(path)
          case _ => None
        }
        case _ => throw new Exception("Error checking for term replacement in "+e1+" and "+e2+": "+eq+" is not an equation!")
      }
    }

    def checkReplacement(s : LambdaExpression, t : LambdaExpression, e1 : LambdaExpression, e2 : LambdaExpression) : ReplacementResult = {
      (e1,e2) match {
        case _ if (e1 == e2) => Equal
        case _ if (e1 == s) && (e2 == t) => EqualModuloEquality(Nil)
        case (Var(_,_), Var(_,_)) => Different
        case (App(l1,r1), App(l2,r2)) =>
          (checkReplacement(s,t,l1,l2), checkReplacement(s,t,r1,r2)) match {
            case (Equal, Equal) => Equal
            case (EqualModuloEquality(path), Equal) => EqualModuloEquality(1::path)
            case (Equal, EqualModuloEquality(path)) => EqualModuloEquality(2::path)
            case _ => Different
          }
        case (Abs(v1,t1), Abs(v2,t2)) => Different
        case _ => Different
      }
    }

  }

  // TODO: implement verification of the rule
  object EquationLeft1Rule {
    /** <pre>Constructs a proof ending with a EqLeft rule.
      * In it, a formula A (marked by term2oc) is replaced by formula main.
      *
      * This rule does not check for the correct use of the =-symbol.
      * The burden of correct usage is on the programmer!
      * 
      * The rule: 
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr, A[T1/a] |- tR
      * ------------------------------------ (EqLeft1)
      *      sL, A[T1/b], tL |- sR, tR
      * </pre>
      * 
      * @param s1 The left proof with the equarion a=b in the succedent in its bottommost sequent.
      * @param s2 The right proof with a formula A[T1/a] in the antecedent of its bottommost sequent,
      *        in which some term T1 has been replaced by the term a. Note that identical terms to
      *        T1 may occur elsewhere in A. These will not be changed.
      *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
      *        This allows selective replacing of terms.
      * @param term1oc The occurrence (a=b) in s1.
      * @param term2oc The occurrence of A[T1/a] in s2.
      * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
      * @return An LK Proof ending with the new inference.
      */ 
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent)
      val succedent = suc1 ++ suc2

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationLeft1RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:l1"
      }
    }

    /** <pre>Constructs a proof ending with a EqLeft rule.
      * In it, a formula A (marked by term2oc) is replaced by formula main.
      * This function merely returns the resulting sequent, not a proof.
      *
      * This rule does not check for the correct use of the =-symbol.
      * The burden of correct usage is on the programmer!
      * 
      * The rule: 
      *     (s1)               (s2)
      * sL |- a=b, sR    tr, A[T1/a] |- tR
      * ------------------------------------ (EqLeft1)
      *      sL, A[T1/b], tL |- sR, tR
      * </pre>
      * 
      * @param s1 The left sequent with the equarion a=b in its succent.
      * @param s2 The right sequent with a formula A[T1/a] in the antecedent of its bottommost sequent,
      *        in which some term T1 has been replaced by the term a. Note that identical terms to
      *        T1 may occur elsewhere in A. These will not be changed.
      *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
      *        This allows selective replacing of terms.
      * @param term1oc The occurrence (a=b) in s1.
      * @param term2oc The occurrence of A[T1/a] in s2.
      * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
      * @return The sequent (sL, A[T1/b], tL |- sR, tR).
      */ 
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent)
      val succedent = suc1 ++ suc2

      Sequent(antecedent, succedent)
    }

    /** <pre>Constructs a proof ending with a EqLeft rule.
      * In it, a formula term2 of the form A[T1/a] is replaced by formula main.
      *
      * This rule does not check for the correct use of the =-symbol.
      * The burden of correct usage is on the programmer!
      * 
      * The rule: 
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr, A[T1/a] |- tR
      * ------------------------------------ (EqLeft1)
      *      sL, A[T1/b], tL |- sR, tR
      * </pre>
      * 
      * @param s1 The left proof with the equarion a=b in the succent in its bottommost sequent.
      * @param s2 The right proof with a formula A[T1/a] in the antecedent of its bottommost sequent,
      *        in which some term T1 has been replaced by the term a. Note that identical terms to
      *        T1 may occur elsewhere in A. These will not be changed.
      *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
      *        This allows selective replacing of terms.
      * @param term1 The formula (a=b) in s1.
      * @param term2 The formula A[T1/a] in s2.
      * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
      * @return An LK Proof ending with the new inference.
      */ 
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationLeft1RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }

  // TODO: implement verification of the rule
  object EquationLeft2Rule {
    /** <pre>See EquationLeft1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
      *
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr, A[T1/b] |- tR
      * ------------------------------------ (EqLeft2)
      *      sL, A[T1/a], tL |- sR, tR
      * </pre>
      */
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {      
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent)
      val succedent = suc1 ++ suc2

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationLeft2RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:l2"
      }
    }

    /** <pre>See EquationLeft1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
      *
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr, A[T1/b] |- tR
      * ------------------------------------ (EqLeft2)
      *      sL, A[T1/a], tL |- sR, tR
      * </pre>
      */
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent.filterNot(_ == auxocc))
      val antecedent = ant1 ++ ant2 :+ prinFormula
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent)
      val succedent = suc1 ++ suc2

      Sequent(antecedent, succedent)
    }

    /** <pre>See EquationLeft1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
      *
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr, A[T1/b] |- tR
      * ------------------------------------ (EqLeft2)
      *      sL, A[T1/a], tL |- sR, tR
      * </pre>
      */
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationLeft2RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }

  // TODO: implement verification of the rule
  object EquationRight1Rule {

    /** <pre>Constructs a proof ending with a EqRight rule.
      * In it, a formula A (marked by term2oc) is replaced by formula main.
      *
      * This rule does not check for the correct use of the =-symbol.
      * The burden of correct usage is on the programmer!
      * 
      * The rule: 
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr |- tR, A[T1/a]
      * ------------------------------------ (EqRight1)
      *      sL, tL |- sR, tR, A[T1/b]
      * </pre>
      * 
      * @param s1 The left proof with the equarion a=b in the succent in its bottommost sequent.
      * @param s2 The right proof with a formula A[T1/a] in the succedent of its bottommost sequent,
      *        in which some term T1 has been replaced by the term a. Note that identical terms to
      *        T1 may occur elsewhere in A. These will not be changed.
      *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
      *        This allows selective replacing of terms.
      * @param term1oc The occurrence (a=b) in s1.
      * @param term2oc The occurrence of A[T1/a] in s2.
      * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
      * @return An LK Proof ending with the new inference.
      */ 
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {      
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationRight1RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:r1"
      }
    }

    /** <pre>Constructs a proof ending with a EqLeft rule.
      * In it, a formula A (marked by term2oc) is replaced by formula main.
      * This function merely returns the resulting sequent, not a proof.
      *
      * This rule does not check for the correct use of the =-symbol.
      * The burden of correct usage is on the programmer!
      * 
      * The rule: 
      *    (s1)               (s2)
      * sL |- a=b, sR    tr |- tR, A[T1/a]
      * ------------------------------------ (EqRight1)
      *      sL, tL |- sR, tR, A[T1/b]
      * </pre>
      * 
      * @param s1 The left sequent with the equarion a=b in its succedent.
      * @param s2 The right sequent with a formula A[T1/a] in the antecedent of its bottommost sequent,
      *        in which some term T1 has been replaced by the term a. Note that identical terms to
      *        T1 may occur elsewhere in A. These will not be changed.
      *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
      *        This allows selective replacing of terms.
      * @param term1oc The occurrence (a=b) in s1.
      * @param term2oc The occurrence of A[T1/a] in s2.
      * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
      * @return The sequent (sL, A[T1/b], tL |- sR, tR).
      */ 
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      Sequent(antecedent, succedent)
    }

    /** <pre>Constructs a proof ending with a EqRight rule.
      * In it, a term2 of the form A[T1/a] is replaced by formula main.
      *
      * This rule does not check for the correct use of the =-symbol.
      * The burden of correct usage is on the programmer!
      * 
      * The rule: 
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr |- tR, A[T1/a]
      * ------------------------------------ (EqRight1)
      *      sL, tL |- sR, tR, A[T1/b]
      * </pre>
      * 
      * @param s1 The left proof with the equarion a=b in the succent in its bottommost sequent.
      * @param s2 The right proof with a formula A[T1/a] in the succedent of its bottommost sequent,
      *        in which some term T1 has been replaced by the term a. Note that identical terms to
      *        T1 may occur elsewhere in A. These will not be changed.
      *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
      *        This allows selective replacing of terms.
      * @param term1 The formula (a=b) in s1.
      * @param term2 The formula A[T1/a] in s2.
      * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
      * @return An LK Proof ending with the new inference.
      */ 
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.succedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationRight1RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }

  // TODO: implement verification of the rule
  object EquationRight2Rule {

    /** <pre>See EquationRight1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
      *
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr |- tR, A[T1/b]
      * ------------------------------------ (EqRight1)
      *      sL, tL |- sR, tR, A[T1/a]
      * </pre>
      */
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {      
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.root.antecedent)
      val ant2 = createContext(s2.root.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.root.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2 )
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = EquationRight2RuleType
        def aux = (eqocc::Nil)::(auxocc::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "e:r2"
      }
    }

    /** <pre>See EquationRight1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
      *
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr |- tR, A[T1/b]
      * ------------------------------------ (EqRight1)
      *      sL, tL |- sR, tR, A[T1/a]
      * </pre>
      */
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, main: HOLFormula) = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = eqocc.factory.createFormulaOccurrence(main, eqocc::auxocc::Nil)

      val ant1 = createContext(s1.antecedent)
      val ant2 = createContext(s2.antecedent)
      val antecedent = ant1 ++ ant2
      val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
      val suc2 = createContext(s2.succedent.filterNot(_ == auxocc))
      val succedent = suc1 ++ suc2 :+ prinFormula

      Sequent(antecedent, succedent)
    }

    /** <pre>See EquationRight1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
      *
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tr |- tR, A[T1/b]
      * ------------------------------------ (EqRight1)
      *      sL, tL |- sR, tR, A[T1/a]
      * </pre>
      */
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.succedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }

    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val eqocc = term1op.get
        val auxocc = term2op.get
        (eqocc, auxocc)
      }
    }

    def unapply(proof: LKProof) = if (proof.rule == EquationRight2RuleType) {
        val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, p1))
      }
      else None
  }
}
