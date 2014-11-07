/*
 * quantificationRules.scala
 *
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol.BetaReduction._
import at.logic.language.hol._
import at.logic.utils.ds.trees._
import base._

case class LKQuantifierException(main : HOLFormula,
				 aux: HOLFormula,
                                 term : HOLExpression,
                                 calculated_formula : HOLFormula,
                                 quantifier_var : HOLVar) extends Exception {
  override def getMessage = "Substituting the variable " + quantifier_var + 
    " with the term " + term + " in the formula " + main + 
    " gives " + calculated_formula + " instead of " + aux
}

// Quantifier rules
case object ForallLeftRuleType extends UnaryRuleTypeA
case object ForallRightRuleType extends UnaryRuleTypeA
case object ExistsLeftRuleType extends UnaryRuleTypeA
case object ExistsRightRuleType extends UnaryRuleTypeA

object ForallLeftRule extends WeakRuleHelper(false) {

  /** <pre>Constructs a proof ending with a ForallLeft rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL, A[term/x] |- sR
    * -------------------- (ForallLeft)
    * sL, Forall x.A |- sR
    * </pre>
    *
    * @param s1 The top proof with (sL, A[term/x] |- sR) as the bottommost sequent.
    * @param aux The formula A[term/x], in which a term is to be all-quantified.
    * @param main The resulting (Forall x.A), with some (not necessarily all) instances of term replaced by a newly introduced variable.
    * @param term The term to be all-quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, term: HOLExpression) : LKProof = {
    s1.root.antecedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, term )
      case _ => throw new LKUnaryRuleCreationException("all:l", s1, aux::Nil)
    }
  }

  /** <pre>Constructs a proof ending with a ForallLeft rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL, A[term/x] |- sR
    * -------------------- (ForallLeft)
    * sL, Forall x.A |- sR
    * </pre>
    *
    * @param s1 The top proof with (sL, A[term/x] |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of the formula A[term/x], in which a term is to be all-quantified.
    * @param main The resulting (Forall x.A), with some (not necessarily all) instances of term replaced by a newly introduced variable.
    * @param term The term to be all-quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: LKProof, term1oc: FormulaOccurrence, main: HOLFormula, term: HOLExpression) : LKProof = {
    try {
      val aux_fo = getTerms(s1.root, term1oc, main, term)
      val prinFormula = getPrinFormula(main, aux_fo)
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1 )
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
        def rule = ForallLeftRuleType
        def aux = (aux_fo::Nil)::Nil
        def prin = prinFormula::Nil
        def subst = term
        override def name = "\u2200:l"
      }
    } catch {
      case e:LKRuleCreationException =>
        throw new LKUnaryRuleCreationException(e.getMessage, s1, Nil)
    }
  }

  /** <pre>All-quantifies a term in a sequent.
    * This function merely returns the resulting sequent, not a proof.
    *
    * The rule:
    *   (rest of s1)
    *  sL, A[term/x] |- sR
    * -------------------- (ForallLeft)
    * sL, Forall x.A |- sR
    * </pre>
    *
    * @param s1 The sequent (sL, A[term/x] |- sR).
    * @param term1oc The formula A[term/x], in which a term is to be all-quantified.
    * @param main The resulting (Forall x.A), with some (not necessarily all) instances of term replaced by a newly introduced variable.
    * @param term The term to be all-quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return The sequent (sL, Forall x.A |- sR).
    */
  def apply(s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula, term: HOLExpression) = {
    val aux_fo = getTerms(s1, term1oc, main, term)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }

  def unapply(proof: LKProof) = if (proof.rule == ForallLeftRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.subst))
  }
  else None
}

object ExistsRightRule extends WeakRuleHelper(true) {

  /** <pre>Constructs a proof ending with an ExistsRight rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL |- sR, A[term/x]
    * -------------------- (ExistsRight)
    * sL |- sR, Exists x.A
    * </pre>
    *
    * @param s1 The top proof with (sL, A[term/x] |- sR) as the bottommost sequent.
    * @param aux The formula A[term/x], in which a term is to be existentially quantified.
    * @param main The resulting (Exists x.A), with some (not necessarily all) instances of term replaced by a newly introduced variable.
    * @param term The term to be existentially quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, term: HOLExpression) : LKProof = {
    s1.root.succedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, term )
      case _ => throw new LKUnaryRuleCreationException("ex:r", s1, aux::Nil)
    }
  }

  /** <pre>Constructs a proof ending with an ExistsRight rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL |- sR, A[term/x]
    * -------------------- (ExistsRight)
    * sL |- sR, Exists x.A
    * </pre>
    *
    * @param s1 The top proof with (sL, A[term/x] |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of the formula A[term/x], in which a term is to be existentially quantified.
    * @param main The resulting (Exists x.A), with some (not necessarily all) instances of term replaced by a newly introduced variable.
    * @param term The term to be existentially quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: LKProof, term1oc: FormulaOccurrence, main: HOLFormula, term: HOLExpression) : LKProof = {
    try {
      val aux_fo = getTerms(s1.root, term1oc, main, term)
      val prinFormula = getPrinFormula(main, aux_fo)
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1 )
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
        def rule = ExistsRightRuleType
        def aux = (aux_fo::Nil)::Nil
        def prin = prinFormula::Nil
        def subst = term
        override def name = "\u2203:r"
      }
    } catch {
      case e:LKRuleCreationException =>
        throw new LKUnaryRuleCreationException(e.getMessage, s1, Nil)
    }
  }

  /** <pre>Constructs a proof ending with an ExistsRight rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL |- sR, A[term/x]
    * -------------------- (ForallLeft)
    * sL |- sR, Exists x.A
    * </pre>
    *
    * @param s1 The top proof with (sL, A[term/x] |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of the formula A[term/x], in which a term is to be all-quantified.
    * @param main The resulting (Exists x.A), with some (not necessarily all) instances of term replaced by a newly introduced variable.
    * @param term The term to be existentially quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula, term: HOLExpression) = {
    val aux_fo = getTerms(s1, term1oc, main, term)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }

  def unapply(proof: LKProof) = if (proof.rule == ExistsRightRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.subst))
  }
  else None
}

object ForallRightRule extends StrongRuleHelper(true) {

  /** <pre>Constructs a proof ending with a ForallRight rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL |- sR, A[y/x]
    * -------------------- (ForallRight)
    * sL |- sR, Forall x.A
    * </pre>
    *
    * @param s1 The top proof with (sL |- sR, A[y/x]) as the bottommost sequent.
    * @param aux The formula A[y/x], in which a free variable y is to be all-quantified.
    * @param main The resulting (Forall x.A), with some (not necessarily all) instances of the free variable eigen_var replaced by a newly introduced variable.
    * @param eigen_var The eigenvariable to be all-quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, eigen_var: HOLVar) : LKProof =
    s1.root.succedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, eigen_var )
      case _ => throw new LKUnaryRuleCreationException("all:r", s1, aux::Nil)
    }

  /** <pre>Constructs a proof ending with a ForallRight rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL |- sR, A[y/x]
    * -------------------- (ForallRight)
    * sL |- sR, Forall x.A
    * </pre>
    *
    * @param s1 The top proof with (sL |- sR, A[y/x]) as the bottommost sequent.
    * @param term1oc The occurrence of the formula A[y/x], in which a free variable y is to be all-quantified.
    * @param main The resulting (Forall x.A), with some (not necessarily all) instances of the free variable eigen_var replaced by a newly introduced variable.
    * @param eigen_var The eigenvariable to be all-quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply( s1: LKProof, term1oc: FormulaOccurrence, main: HOLFormula, eigen_var: HOLVar ) : LKProof = {
    try {
      val aux_fo = getTerms(s1.root, term1oc, main, eigen_var)
      val prinFormula = getPrinFormula(main, aux_fo)
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1 )
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
          def rule = ForallRightRuleType
          def aux = (aux_fo::Nil)::Nil
          def prin = prinFormula::Nil
          def eigenvar = eigen_var
          override def name = "\u2200:r"
        }
    } catch {
      case e:LKRuleCreationException =>
        throw new LKUnaryRuleCreationException(e.getMessage, s1, Nil)
    }
  }

  /** <pre>Constructs a proof ending with a ForallRight rule.
    * This function merely returns the resulting sequent, not a proof.
    *
    * The rule:
    *   (rest of s1)
    *  sL |- sR, A[y/x]
    * -------------------- (ForallRight)
    * sL |- sR, Forall x.A
    * </pre>
    *
    * @param s1 The sequent (sL |- sR, A[y/x]).
    * @param term1oc The formula A[y/x], in which a free variable y is to be all-quantified.
    * @param main The resulting (Forall x.A), with some (not necessarily all) instances of the free variable eigen_var replaced by a newly introduced variable.
    * @param eigen_var The eigenvariable to be all-quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return The sequent (sL |- sR, Forall x.A).
    */
  def apply( s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula, eigen_var: HOLVar ) = {
    val aux_fo = getTerms(s1, term1oc, main, eigen_var)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }


  def unapply(proof: LKProof) = if (proof.rule == ForallRightRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.eigenvar))
  }
  else None
}

object ExistsLeftRule extends StrongRuleHelper(false) {

  /** <pre>Constructs a proof ending with a ExistsLeft rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL, A[y/x] |- sR
    * -------------------- (ExistsLeft)
    * sL, Exists x.A |- sR
    * </pre>
    *
    * @param s1 The top proof with (sL, A[y/x] |- sR) as the bottommost sequent.
    * @param aux The formula A[y/x], in which a free variable y is to be existentially quantified.
    * @param main The resulting (Exists x.A), with some (not necessarily all) instances of the free variable eigen_var replaced by a newly introduced variable.
    * @param eigen_var The eigenvariable to be existentially quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: LKProof, aux: HOLFormula, main: HOLFormula, eigen_var: HOLVar) : LKProof =
    s1.root.antecedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, eigen_var )
      case _ => throw new LKUnaryRuleCreationException("ex:l", s1, aux::Nil)
    }

  /** <pre>Constructs a proof ending with a ExistsLeft rule.
    *
    * The rule:
    *   (rest of s1)
    *  sL, A[y/x] |- sR
    * -------------------- (ExistsLeft)
    * sL, Exists x.A |- sR
    * </pre>
    *
    * @param s1 The top proof with (sL, A[y/x] |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of the formula A[y/x], in which a free variable y is to be existentially quantified.
    * @param main The resulting (Exists x.A), with some (not necessarily all) instances of the free variable eigen_var replaced by a newly introduced variable.
    * @param eigen_var The eigenvariable to be existentially quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return An LK Proof ending with the new inference.
    */
  def apply( s1: LKProof, term1oc: FormulaOccurrence, main: HOLFormula, eigen_var: HOLVar ) : LKProof = {
    try {
      val aux_fo = getTerms(s1.root, term1oc, main, eigen_var)
      val prinFormula = getPrinFormula(main, aux_fo)
      val sequent = getSequent(s1.root, aux_fo, prinFormula)

      new UnaryTree[Sequent](sequent, s1)
        with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
        def rule = ExistsLeftRuleType
        def aux = (aux_fo::Nil)::Nil
        def prin = prinFormula::Nil
        def eigenvar = eigen_var
        override def name = "\u2203:l"
      }
    } catch {
      case e:LKRuleCreationException =>
        throw new LKUnaryRuleCreationException(e.getMessage, s1, Nil)
    }
  }

  /** <pre>Constructs a proof ending with a ExistsLeft rule.
    * This function merely returns the resulting sequent, not a proof.
    *
    * The rule:
    *   (rest of s1)
    *  sL, A[y/x] |- sR
    * -------------------- (ExistsLeft)
    * sL, A[y/x] |- sR
    * </pre>
    *
    * @param s1 The sequent (sL, A[y/x] |- sR).
    * @param term1oc The formula A[y/x], in which a free variable y is to be existentially quantified.
    * @param main The resulting (Forall x.A), with some (not necessarily all) instances of the free variable eigen_var replaced by a newly introduced variable.
    * @param eigen_var The eigenvariable to be existentially quantified & whose substitution into the main formula yields the auxiliary formula.
    * @return The sequent (sL, Exists x.A |- sR).
    */
  def apply( s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula, eigen_var: HOLVar ) = {
    val aux_fo = getTerms(s1, term1oc, main, eigen_var)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }

  def unapply(proof: LKProof) = if (proof.rule == ExistsLeftRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.eigenvar))
  }
  else None
}


class QuantifierRuleHelper(polarity : Boolean) {
  private[lk] def getPrinFormula(main: HOLFormula, aux_fo: FormulaOccurrence) = {
    aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
  }

  private[lk] def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    if (polarity == false) {
      //working on antecedent {
      val ant = createContext(s1.antecedent.filterNot(_ == aux_fo))
      val antecedent = ant :+ prinFormula
      val succedent = createContext(s1.succedent)
      Sequent(antecedent, succedent)
    } else {
      //working on succedent
      val antecedent = createContext(s1.antecedent)
      val suc = createContext(s1.succedent.filterNot(_ == aux_fo))
      val succedent = suc :+ prinFormula
      Sequent(antecedent, succedent)
    }

  }
}

class StrongRuleHelper(polarity : Boolean) extends QuantifierRuleHelper(polarity) {
  private[lk] def getTerms(s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula, eigen_var: HOLVar) = {
    val foccs = if (polarity==false) s1.antecedent else s1.succedent
    foccs.find(_ == term1oc) match {
    case None => throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    case Some(aux_fo) =>
      main match {
        case AllVar( x, sub) =>
          // eigenvar condition
          assert( ( s1.antecedent ++ (s1.succedent.filterNot(_ == aux_fo)) ).forall( fo => !freeVariables(fo.formula).contains( eigen_var ) ),
            "Eigenvariable " + eigen_var + " occurs in context " + s1 )

          val back_substitiution = Substitution(x,eigen_var)

          //This check does the following: if we conclude exists x.A[x] from A[t] then A[x\t] must be A[t].
          //If it fails, you are doing something seriously wrong!
          //In any case do NOT remove it without telling everyone!
          //assert( betaNormalize( HOLApp( sub, eigen_var ) ) == aux_fo.formula , "assert 2 in getTerms of String Quantifier Rule fails!\n"+betaNormalize( HOLApp( sub, eigen_var ) )+" != "+aux_fo.formula)
          assert( betaNormalize( back_substitiution(sub) ) == aux_fo.formula , "assert 2 in getTerms of String Quantifier Rule fails!\n"+betaNormalize( HOLApp( sub, eigen_var ) )+" != "+aux_fo.formula)
          aux_fo

        case ExVar( x, sub) =>
          // eigenvar condition
          assert( ( (s1.antecedent.filterNot(_ == aux_fo)) ++ s1.succedent ).forall( fo => !freeVariables(fo.formula).contains( eigen_var ) ),
            "Eigenvariable " + eigen_var + " occurs in context " + s1 )

          val back_substitiution = Substitution(x,eigen_var)

          //This check does the following: if we conclude exists x.A[x] from A[t] then A[x\t] must be A[t].
          //If it fails, you are doing something seriously wrong!
          //In any case do NOT remove it without telling everyone!
          //assert( betaNormalize( HOLApp( sub, eigen_var ) ) == aux_fo.formula )
          assert( betaNormalize( back_substitiution(sub) ) == aux_fo.formula , "assert 2 in getTerms of String Quantifier Rule fails!\n"+betaNormalize( HOLApp( sub, eigen_var ) )+" != "+aux_fo.formula)
          aux_fo

        case _ => throw new LKRuleCreationException("Main formula of a quantifier rule must start with a strong quantfier.")
      }
    }
  }
}

class WeakRuleHelper(polarity : Boolean) extends QuantifierRuleHelper(polarity) {
  def computeAux( main: HOLFormula, term: HOLExpression ) = main match {
    case AllVar( v, sub ) =>
      val s = Substitution(v, term)
      (v, betaNormalize( s(sub) ))
    case ExVar( v, sub ) =>
      val s = Substitution(v, term)
      (v, betaNormalize( s(sub) ))
    case _ => throw new LKRuleCreationException("Main formula of a quantifier rule must start with a strong quantfier.")
  }

  private[lk] def getTerms(s1: Sequent, term1oc: FormulaOccurrence, main: HOLFormula, term: HOLExpression) = {
    val foccs = if (polarity==false) s1.antecedent else s1.succedent
    foccs.find(_ == term1oc) match {
      case None => throw new LKRuleCreationException("Auxiliary formulas are not contained in the correct part of the sequent!")
      case Some(aux_fo) =>
        val (v, comp_aux) = computeAux( main, term )
        //This check does the following: if we conclude exists x.A[x] from A[t] then A[x\t] must be A[t].
        //If it fails, you are doing something seriously wrong!
        //In any case do NOT remove it without telling everyone!
        if (comp_aux != aux_fo.formula)
          throw new LKQuantifierException(main, aux_fo.formula, term, comp_aux, v)
        aux_fo
    }
  }
}

