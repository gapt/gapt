/*
 * propositionalRules.scala
 *
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.trees._
import base._

// axioms
case object InitialRuleType extends NullaryRuleTypeA

// structural rules
case object WeakeningLeftRuleType extends UnaryRuleTypeA
case object WeakeningRightRuleType extends UnaryRuleTypeA
case object ContractionLeftRuleType extends UnaryRuleTypeA
case object ContractionRightRuleType extends UnaryRuleTypeA
case object CutRuleType extends BinaryRuleTypeA

// Propositional rules
case object AndRightRuleType extends BinaryRuleTypeA
case object AndLeft1RuleType extends UnaryRuleTypeA
case object AndLeft2RuleType extends UnaryRuleTypeA
case object OrRight1RuleType extends UnaryRuleTypeA
case object OrRight2RuleType extends UnaryRuleTypeA
case object OrLeftRuleType extends BinaryRuleTypeA
case object ImpRightRuleType extends UnaryRuleTypeA
case object ImpLeftRuleType extends BinaryRuleTypeA
case object NegLeftRuleType extends UnaryRuleTypeA
case object NegRightRuleType extends UnaryRuleTypeA


// lk proofs
// rules are extracted in the form (UpperSequent(s), LowerSequent, AuxiliaryFormula(s), PrincipalFormula(s))

// actual rule extractor/factories
// Axioms (and weakenings) always return a pair(Proof, mapping) which maps the indices of the list given into the new occurrences.
// It is used together with an implicit conversion between this pair into a proof so users who are not interested in this information will not see it

object Axiom {

  /** <pre>Creates an axiom with the sequent seq (consisting of the
    * antecedent sL and the succedent sR).
    * sL and sR have to have a shared formula.
    *
    * The rule: 
    * 
    * ------------(Axiom)
    *   sL |- sR
    * </pre>
    *
    * @param seq The sequent of the axiom.
    * @return The LKProof consisting of s1 as its axiom.
  */
  def apply(seq: Sequent) : LeafTree[Sequent] with NullaryLKProof = {
    if (seq.antecedent.exists((fo:FormulaOccurrence) => (fo.parents.size > 0) ))
      throw new LKRuleCreationException("Ancestor of an occurence in antecedent of Axiom rule is nonempty!")
    if (seq.succedent.exists((fo:FormulaOccurrence) => (fo.parents.size > 0) ))
      throw new LKRuleCreationException("Ancestor of an occurence in succedent of Axiom rule is nonempty!")

    new LeafTree[Sequent](seq) with NullaryLKProof {def rule = InitialRuleType}
  }

  /** <pre>Creates an axiom consisting of the antecedent ant and
    * the succeedent suc. ant and suc have to have a shared formula.
    *
    * The rule: 
    * 
    * ------------(Axiom)
    *  ant |- suc
    * </pre>
    *
    * @param ant The antecedent the axiom.
    * @param suc The succedent of the axiom.
    * @return The LKProof consisting of (ant |- suc) as its axiom.
    */
  def apply[T](ant: Seq[Formula], suc: Seq[Formula]) (implicit factory: FOFactory): LeafTree[Sequent] with NullaryLKProof = {
    val left: Seq[FormulaOccurrence] = ant.map(x => factory.createFormulaOccurrence(x.asInstanceOf[HOLFormula], Nil))
    val right: Seq[FormulaOccurrence] = suc.map(x => factory.createFormulaOccurrence(x.asInstanceOf[HOLFormula], Nil))
    new LeafTree[Sequent](Sequent(left, right)) with NullaryLKProof {def rule = InitialRuleType}
  }

  def apply(seq: FSequent)(implicit factory: FOFactory): LeafTree[Sequent] with NullaryLKProof = apply(seq.antecedent, seq.succedent)

  def unapply(proof: LKProof) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
}

object WeakeningLeftRule {

  /** <pre>Introduces a formula into the left side of a sequent.
    *
    * The rule: 
    *         (rest of s1)
    *  sL |- sR
    * ------------ (WeakeningLeft)
    * sL, f |- sR
    * </pre>
    *
    * @param s1 The top proof with (sL |- sR) as the bottommost sequent.
    * @param f The formula to introduce below s1.
    *
    * @return An LKProof ending with the new inference.
    */ 
  def apply(s1: LKProof, f: HOLFormula) (implicit factory: FOFactory) = {
    val prinFormula = getPrinFormula(f)
    val sequent = getSequent(s1.root, prinFormula)
    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with PrincipalFormulas {
        def rule = WeakeningLeftRuleType
        def prin = prinFormula::Nil
        override def name = "w:l"
      }
  }

  /** Introduces a formula into the antecedent of a sequent. This method
    * merely returns an extended sequent, not a proof.
    *
    * @param s1 The sequent whose antecedent is to be weakened.
    * @param f The formula to introduce into s1.
    *
    * @return The sequent s1, with the antecedent extended by f.
    */ 
  def apply(s1 : Sequent, f : HOLFormula)(implicit factory : FOFactory) = {
    val prinFormula = getPrinFormula(f)
    getSequent(s1, prinFormula)
  }
  private def getPrinFormula(f: HOLFormula) = {
    factory.createFormulaOccurrence(f, Nil)
  }
  private def getSequent(s1: Sequent, prinFormula: FormulaOccurrence) = {
    Sequent(createContext(s1.antecedent) :+ prinFormula, createContext(s1.succedent))
  }
  def unapply(proof: LKProof) = if (proof.rule == WeakeningLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, p1))
    }
    else None
}


object WeakeningRightRule {
  /** <pre>Introduces a formula into the succedent of a sequent.
    *
    * The rule:
    *  (rest of s1)
    *   sL |- sR
    * ------------- (WeakeningRight)
    *  sL |- sR, f
    * </pre>
    *
    * @param s1 The top proof with (sL |- sR) as the bottommost sequent.
    * @param f The formula to introduce below s1.
    * @return An LKProof ending with the new inference.
    */
  def apply(s1: LKProof, f: HOLFormula) (implicit factory: FOFactory) = {
    val prinFormula = getPrinFormula(f)
    val sequent = getSequent(s1.root, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with PrincipalFormulas {
        def rule = WeakeningRightRuleType
        def prin = prinFormula::Nil
        override def name = "w:r"
      }
  }

  /** Introduces a formula into the succedent of a sequent. This method
    * merely returns an extended sequent, not a proof.
    *
    * @param s1 The sequent whose succedent is to be weakened.
    * @param f The formula to introduce into s1.
    *
    * @return The sequent s1, with the succedent extended by f.
    */ 
  def apply(s1 : Sequent, f : HOLFormula)(implicit factory : FOFactory) = {
    val prinFormula = getPrinFormula(f)
    getSequent(s1, prinFormula)
  }
  private def getPrinFormula(f: HOLFormula) = {
    factory.createFormulaOccurrence(f, Nil)
  }
  private def getSequent(s1: Sequent, prinFormula: FormulaOccurrence) = {
    Sequent(createContext(s1.antecedent), createContext(s1.succedent) :+ prinFormula)
  }
  def unapply(proof: LKProof) = if (proof.rule == WeakeningRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, p1))
    }
    else None
}

object ContractionLeftRule {

  /** <pre>Eliminates a duplicate occurrence of a formula F
    * (marked by term1oc and term2oc) from the antecedent of a sequent. 
    * 
    * The rule: 
    *  (rest of s1)
    * sL, F, F |- sR
    * --------------- (ContractionLeft)
    * sL, F |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, F, F |- sR) as the bottommost sequent.
    * @param term1oc The first occurrence of F
    * @param term2oc The second occurrence of F
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term1, term2, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = ContractionLeftRuleType
        def aux = (term1::term2::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "c:l"
      }
  }

/** Eliminates a duplicate occurrence of a formula F
  * (marked by term1oc and term2oc) from the antecedent of a sequent. 
  * This method merely returns the changed sequent, not a proof.
  * 
  * @param s1 The sequent (sL, F, F |- sR).
  * @param term1oc The first occurrence of F
  * @param term2oc The second occurrence of F
  * @return The sequent (sL, F |- sR).
  */ 
  def apply(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term1, term2, prinFormula)
  }

/** <pre>Eliminates a duplicate occurrence of a formula term1
  * from the antecedent of a sequent. The two occurrences are automatically
  * chosen; if term1 occurs less than twice, an exception is thrown.
  * If term1 occurs more than twice, multiple applications of this
  * function are needed to remove all duplicate occurrences.
  * 
  * The rule: 
  *  (rest of s1)
  * sL, term1, term1 |- sR
  * ----------------------- (ContractionLeft)
  * sL, term1 |- sR
  * </pre>
  * 
  * @param s1 The top proof with (sL, term1, term1 |- sR) as the bottommost sequent.
  * @param term1 The formula whose duplicate occurrence is to be removed.
  * @return An LK Proof ending with the new inference.
  */ 
  def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
    (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
      case (x::y::_) => apply(s1, x, y)
      case _ => //throw new LKRuleCreationException("Not matching formula occurrences found in " + s1.root.antecedent.map(_.formula) +
        //" for application of the rule with the given formula: " + term1)
        throw new LKUnaryRuleCreationException("c:l", s1, term1::Nil)
    }
  }

  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    val term2op = s1.antecedent.find(_ == term2oc)
    if (term1op == None) throw new LKRuleCreationException("Auxiliary formula "+term1oc+" not contained in antecedent "+s1.antecedent+".")
    else if (term2op == None) throw new LKRuleCreationException("Auxiliary formula "+term2oc+" not contained in antecedent "+s1.antecedent+".")
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula + ", term2.formula = " + term2.formula)
      else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
      else {
        (term1, term2)
      }
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula
    term1.factory.createFormulaOccurrence(holterm1, term1::term2::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val ant1 = createContext(s1.antecedent.filterNot(x => x == term1 || x == term2))
    val antecedent = ant1 :+ prinFormula
    val succedent = createContext(s1.succedent)
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ContractionLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::a2::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, a2, p1))
    }
    else None
}

object ContractionRightRule {

  /** <pre>Eliminates a duplicate occurrence of a formula F
    * (marked by term1oc and term2oc) from the succedent of a sequent. 
    * 
    * The rule: 
    *  (rest of s1)
    * sL |- sR, F, F
    * --------------- (ContractionRight)
    * sL |- sR, F
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, F, F) as the bottommost sequent.
    * @param term1oc The first occurrence of F
    * @param term2oc The second occurrence of F
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term1, term2, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = ContractionRightRuleType
        def aux = (term1::term2::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "c:r"
      }
  }

  /** Eliminates a duplicate occurrence of a formula F
    * (marked by term1oc and term2oc) from the succecedent of a sequent. 
    * This method merely returns the changed sequent, not a proof.
    * 
    * @param s1 The sequent (sL |- sR, F, F).
    * @param term1oc The first occurrence of F
    * @param term2oc The second occurrence of F
    * @return The sequent (sL |- sR, F).
    */ 
  def apply(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term1, term2, prinFormula)
  }
  
  /** <pre>Eliminates a duplicate occurrence of a formula term1
    * from the succedent of a sequent. The two occurrences are automatically
    * chosen; if term1 occurs less than twice, an exception is thrown.
    * If term1 occurs more than twice, multiple applications of this
    * function are needed to remove all duplicate occurrences.
    * 
    * The rule: 
    *  (rest of s1)
    * sL |- sR, term1, term1
    * ----------------------- (ContractionRight)
    * sL |- sR, term1
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, term1, term1) as the bottommost sequent.
    * @param term1 The formula whose duplicate occurrence is to be removed.
    * @return An LK Proof ending with the new inference.
    */ 
    def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
    val occurrences = s1.root.succedent.filter(x => x.formula == term1).toList
      occurrences match {
        case (x::y::_) =>
          apply(s1, x, y)
        case _ =>
          throw new LKUnaryRuleCreationException("c:r", s1, term1::Nil)
        //throw new LKRuleCreationException("No matching formula occurrences found in " + s1.root.antecedent.map(_.formula) +
          //" for application of the rule c:l with the given formula: " + term1)
      }
    }

  private def getTerms(s1 : Sequent, term1oc : FormulaOccurrence, term2oc : FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    val term2op = s1.succedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      if (term1.formula != term2.formula) throw new
        LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula + ", term2.formula = " + term2.formula)
      else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
      else {
        (term1, term2)
      }
    }
  }

  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula
    term1.factory.createFormulaOccurrence(holterm1, term1::term2::Nil)
  }

  private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent)
    val suc1 = createContext(s1.succedent.filterNot(x =>  x == term1 || x == term2))
    val succedent = suc1 :+ prinFormula
    Sequent(antecedent, succedent)
  }

  def unapply(proof: LKProof) = if (proof.rule == ContractionRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::a2::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, a2, p1))
    }
    else None
}

object CutRule {
  /** <pre>Cuts a common formula F (marked by term1oc in the
    * succedent of s1 and by term2oc in the antecedent of s2)
    * from two proofs s1 & s2.
    *
    * Let s1 have (sL |- sR, F) as its bottommost sequent and
    * let s2 have (tL, F |- tR) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- sR, F        tL, F |- tR
    * ------------------------------ (Cut)
    *       sL, tL |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with F in the succedent of its bottommost sequent.
    * @param s2: The right proof with F in the antecedent of its bottommost sequent.
    * @param term1oc The occurrence of F in s1.
    * @param term2oc The occurrence of F in s2.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL |- sR, tR) as its bottommost sequent.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val sequent = getSequent(s1.root, s2.root, term1, term2)

    new BinaryTree[Sequent](sequent, s1, s2)
      with BinaryLKProof with AuxiliaryFormulas {
          def rule = CutRuleType
          def aux = (term1::Nil)::(term2::Nil)::Nil
          override def name = "cut"
      }
  }

  /** <pre>Cuts a common formula F (marked by term1oc in the
    * succedent of s1 and by term2oc in the antecedent of s2)
    * from two proofs s1 & s2. This function merely returns the
    * resulting sequent, not a proof.
    *
    * Let s1 have (sL |- sR, F) as its bottommost sequent and
    * let s2 have (tL, F |- tR) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- sR, F        tL, F |- tR
    * ------------------------------ (Cut)
    *       sL, tL |- sR, tR
    * </pre>
    * 
    * @param s1 The left sequent.
    * @param s2 The right sequent.
    * @param term1oc The occurrence of F in s1.
    * @param term2oc The occurrence of F in s2.
    * @return The sequent (sL, tL |- sR, tR).
    */ 
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
    getSequent(s1, s2, term1, term2)
  }

  /** <pre>Cuts a common formula term1 (found in the succedent of s1 and
    * the antecedent of s2) from two proofs s1 & s2.
    * F is automatically determined. If term1 occurs more than once,
    * only the first occurrence is cut.
    *
    * Let s1 have (sL |- sR, term1) as its bottommost sequent and
    * let s2 have (tL, term1 |- tR) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- sR, term1   tL, term1 |- tR
    * --------------------------------- (Cut)
    *          sL, tL |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with term1 in the succedent of its bottommost sequent.
    * @param s2 The right proof with term1 in the antecedent of its bottommost sequent.
    * @param term1: The formula to be cut.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL |- sR, tR) as its bottommost sequent.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas  = {
    ((s1.root.succedent.filter(x => x.formula.syntaxEquals(term1))).toList,(s2.root.antecedent.filter(x => x.formula.syntaxEquals(term1))).toList) match {
      case ((x::_),(y::_)) => apply(s1, s2, x, y)
      case (Nil,Nil) =>throw new LKRuleCreationException("Not matching formula occurrences found in both " + s1.root.succedent + " and " +
        s2.root.antecedent + " for application of the rule with the given formula " + term1)
      case (Nil,_) =>throw new LKRuleCreationException("Not matching formula occurrences found in " + s1.root.succedent +
        " for application of the rule with the given formula " + term1)
      case (_,Nil) =>throw new LKRuleCreationException("Not matching formula occurrences found in " + s2.root.antecedent +
        " for application of the rule with the given formula " + term1)
    }
  }

  private def getTerms(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    val term2op = s2.antecedent.find(_ == term2oc)
    if (term1op == None || term2op == None) {
      val s1str = s1.succedent.head.toString()
      val s2str = s2.antecedent.head.toString()
      val t1str = term1oc.asInstanceOf[FormulaOccurrence].formula.toString()
      val t2str = term2oc.asInstanceOf[FormulaOccurrence].formula.toString()
      val str = "s1: " + s1str + "\ns2: " + s2str + "\nt1: " + t1str + "\nt2: " + t2str + "\n"
      throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent\n" + str)
    }
    else {
      val term1 = term1op.get
      val term2 = term2op.get
//      if (!term1.formula.syntaxEquals(term2.formula)) throw new LKRuleCreationException("Formulas to be cut are not identical")
      //TODO: check if any algorithm depends on the syntactical equality
      if (term1.formula != term2.formula) throw new LKRuleCreationException("Formulas to be cut are not identical")
      else {
        (term1, term2)
      }
    }
  }

  private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val ant1 = createContext(s1.antecedent)
    val ant2 = createContext(s2.antecedent.filterNot(_ == term2))
    val antecedent = ant1 ++ ant2
    val suc1 = createContext(s1.succedent.filterNot(_ == term1))
    val suc2 = createContext(s2.succedent)
    val succedent = suc1 ++ suc2
    Sequent(antecedent, succedent)
  }

  def unapply(proof: LKProof) = if (proof.rule == CutRuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas]
      val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
      Some((r.uProof1, r.uProof2, r.root, a1, a2))
    }
    else None
}

object AndRightRule {
  /** Returns the left subformula.
    * @param main A formula of the form l And r
    * @return l.
    */
  def computeLeftAux( main: HOLFormula ) = main match { case And(l, _) => l }

  /** Returns the right subformula.
    * @param main A formula of the form l And r
    * @return r.
    */
  def computeRightAux( main: HOLFormula ) = main match { case And(_, r) => r }

  /** <pre>Merges two formulas A & B (marked by term1oc & term2oc in the
    * succedents of s1 & s2) into a conjunction A And B.
    *
    * Let s1 have (sL |- sR, A) as its bottommost sequent and
    * let s2 have (tL |- tR, B) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- sR, A        tL |- tR, B
    * ------------------------------ (AndRight)
    *    sL, tL |- sR, tR, A ∧ B
    * </pre>
    * 
    * @param s1 The left proof with A in the succedent of its bottommost sequent.
    * @param s2 The right proof with B in the succedent of its bottommost sequent.
    * @param term1oc The occurrence of A in s1.
    * @param term2oc The occurrence of B in s2.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL |- sR, tR, A ∧ B) as its bottommost sequent.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, s2.root, term1, term2, prinFormula)

    new BinaryTree[Sequent](sequent, s1, s2)
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = AndRightRuleType
        def aux = ((term1)::Nil)::(term2::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2227:r"
      }
   }

    /** <pre>Merges two formulas A & B (marked by term1oc & term2oc in the
      * succedents of s1 & s2) into a conjunction A And B.
      * This function merely returns the resulting sequent, not a proof.
      *
      * Let s1 be the sequent (sL |- sR, A).
      * let s2 be the sequent (tL |- tR, B).
      * The function returns (sL, tL |- sR, tR, A ∧ B).
      * </pre>
      * 
      * @param s1 The left sequent.
      * @param s2 The right sequent.
      * @param term1oc The occurrence of A in s1.
      * @param term2oc The occurrence of B in s2.
      * @return The sequent (sL, tL |- sR, tR, A ∧ B).
      */ 
    def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
      val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, s2, term1, term2, prinFormula)
    }

    /** <pre>Merges two formulas term1 & term2 into a conjunction A And B.
      * If term1 and/or term2 occur more than once each, only one occurrence
      * of each is merged.
      *
      * Let s1 have (sL |- sR, term1) as its bottommost sequent and
      * let s2 have (tL |- tR, term2) as its bottommost sequent.
      * 
      * The rule: 
      * (rest of s1)             (rest of s2)
      * sL |- sR, term1        tL |- tR, term2
      * -------------------------------------- (AndRight)
      *    sL, tL |- sR, tR, term1 ∧ term2
      * </pre>
      * 
      * @param s1 The left proof with A in the succedent of its bottommost sequent.
      * @param s2 The right proof with B in the succedent of its bottommost sequent.
      * @param term1 The left part of the conjunction in s1.
      * @param term2 The right part of the conjunction in s2.
      * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL |- sR, tR, term1 ∧ term2) as its bottommost sequent.
      */ 
    def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula): BinaryLKProof with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.succedent.filter(x => x.formula == term2)).toList) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y)
        case _ =>
          //throw new LKRuleCreationException("No matching formula occurrences found for application of the rule and:r with the given formulas "
          //+term1+" in "+s1.root+" and "+term2+ " in "+s2.root)
          throw new LKBinaryRuleCreationException("and:r", s1, term1, s2, term2)

      }
  }

    private def getTerms(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s2.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        (term1, term2)
      }
    }

  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula
    val holterm2 = term2.formula
    val form = And(holterm1, holterm2)
    term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
  }

  private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val ant1 = createContext(s1.antecedent)
    val ant2 = createContext(s2.antecedent)
    val antecedent = ant1 ++ ant2
    val suc1 = createContext(s1.succedent.filterNot(_ == term1))
    val suc2 = createContext(s2.succedent.filterNot(_ == term2))
    val succedent = suc1 ++ suc2 :+ prinFormula
    Sequent(antecedent, succedent)
  }

  def unapply(proof: LKProof) = if (proof.rule == AndRightRuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
    }
    else None
}

object AndLeft1Rule {

  /** Returns the left subformula.
    * @param main A formula of the form l And r
    * @return l.
    */
  def computeAux( main: HOLFormula ) = main match { case And(l, _) => l }

  /** <pre>Replaces a formula F (marked by term1oc) with the conjunction
    * F ∧ term2 in the antecedent of a sequent.
    * 
    * The rule: 
    *     (rest of s1)
    *     sL, F |- sR
    * ------------------- (AndLeft1)
    * sL, F ∧ term2 |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, F |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of F in the antecedent of s1.
    * @param term2 The new term to add.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2: HOLFormula) = {
    val term1 = getTerms(s1.root, term1oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term1, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = AndLeft1RuleType
        def aux = (term1::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2227:l1"
      }
  }

  /** Replaces a formula F (marked by term1oc) with the conjunction
    * F ∧ term2 in the antecedent of a sequent. This function merely
    * returns a sequent, not a proof.
    * 
    * @param s1 The sequent (sL, F |- sR).
    * @param term1oc The occurrence of F in the antecedent of s1
    * @param term2 The new term to add.
    * @return The sequent (sL, F ∧ term2 |- sR).
    */
  def apply(s1: Sequent, term1oc: FormulaOccurrence, term2: HOLFormula) = {
    val term1 = getTerms(s1, term1oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term1, prinFormula)
  }

  /** <pre>Replaces a formula term1 with the conjunction
    * term1 ∧ term2 in the antecedent of a sequent.
    * If term1 occurs more than once, only one occurrence is replaced.
    * 
    * The rule: 
    *     (rest of s1)
    *   sL, term1 |- sR
    * ----------------------- (AndLeft1)
    * sL, term1 ∧ term2 |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, term1 |- sR) as the bottommost sequent.
    * @param term1 The term to be replaced by the new conjunct.
    * @param term2 The new term to add.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
      case (x::_) => apply(s1, x, term2)
      case _ => //throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
                throw new LKUnaryRuleCreationException("and:l", s1, term1::term2::Nil)
    }
  }

  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the left part of the sequent")
    else {
      val term1 = term1op.get
      term1
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence, term2: HOLFormula) = {
    val holterm1 = term1.formula
    val form = And(holterm1, term2)
    term1.factory.createFormulaOccurrence(form, term1::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent.filterNot(_ == term1)) :+ prinFormula
    val succedent = createContext(s1.succedent)
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == AndLeft1RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object AndLeft2Rule {

  /** Returns the right subformula.
    * @param main A formula of the form l And r
    * @return l.
    */
  def computeAux( main: HOLFormula ) = main match { case And(_, r) => r }

  /** <pre>Replaces a formula F (marked by term2oc) with the conjunction
    * term1 ∧ F in the antecedent of a sequent.
    * 
    * The rule: 
    *     (rest of s1)
    *     sL, F |- sR
    * ------------------- (AndLeft2)
    * sL, term1 ∧ F |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, F |- sR) as the bottommost sequent.
    * @param term1 The new term to add.
    * @param term2oc The occurrence of F in the antecedent of s1
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2oc: FormulaOccurrence) = {
    val term2 = getTerms(s1.root, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term2, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = AndLeft2RuleType
        def aux = (term2::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2227:l2"
      }
  }

  /** Replaces a formula F (marked by term2oc) with the conjunction
    * term1 ∧ F in the antecedent of a sequent. This function merely
    * returns a sequent, not a proof.
    * 
    * @param s1 The sequent (sL, F |- sR).
    * @param term1 The new term to add.
    * @param term2oc The occurrence of F in the antecedent of s1
    * @return The sequent (sL, F ∧ term2 |- sR).
    */
  def apply(s1: Sequent, term1: HOLFormula, term2oc: FormulaOccurrence) = {
    val term2 = getTerms(s1, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term2, prinFormula)
  }

  /** <pre>Replaces a formula term2 with the conjunction
    * term1 ∧ term2 in the antecedent of a sequent.
    * If term1 occurs more than once, only one occurrence is replaced.
    * 
    * The rule: 
    *     (rest of s1)
    *   sL, term2 |- sR
    * ----------------------- (AndLeft2)
    * sL, term1 ∧ term2 |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, term2 |- sR) as the bottommost sequent.
    * @param term1 The new term to add.
    * @param term2 The term to be replaced by the new conjunct.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    (s1.root.antecedent.filter(x => x.formula == term2)).toList match {
      case (x::_) => apply(s1, term1, x)
      case _ => //throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
                throw new LKUnaryRuleCreationException("and:l", s1, term1::term2::Nil)
    }
  }

  private def getTerms(s1: Sequent, term2oc: FormulaOccurrence) = {
    val term2op = s1.antecedent.find(_ == term2oc)
    if (term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the left part of the sequent")
    else {
      val term2 = term2op.get
      term2
    }
  }

  private def getPrinFormula(term1: HOLFormula, term2: FormulaOccurrence) = {
    val holterm2 = term2.formula
    val form = And(term1, holterm2)
    term2.factory.createFormulaOccurrence(form, term2::Nil)
  }

  private def getSequent(s1: Sequent, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent.filterNot(_ == term2)) :+ prinFormula
    val succedent = createContext(s1.succedent)
    Sequent(antecedent, succedent)
  }

  def unapply(proof: LKProof) = if (proof.rule == AndLeft2RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object OrLeftRule {
  /** Returns the left subformula.
    * @param main A formula of the form l Or r
    * @return l.
    */
  def computeLeftAux( main: HOLFormula ) = main match { case Or(l, _) => l }

  /** Returns the left subformula.
    * @param main A formula of the form l Or r
    * @return r.
    */
  def computeRightAux( main: HOLFormula ) = main match { case Or(_, r) => r }

  /** <pre>Merges two formulas A & B (marked by term1oc & term2oc in the
    * antecedents of s1 & s2) into a disjunction A Or B.
    *
    * Let s1 have (sL, A |- sR) as its bottommost sequent and
    * let s2 have (tL, B |- tR) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL, A |- sR        tL, B |- tR
    * ------------------------------ (OrLeft)
    *    sL, tL, A v B |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with A in the antecedent of its bottommost sequent.
    * @param s2 The right proof with B in the antecedent of its bottommost sequent.
    * @param term1oc The occurrence of A in s1.
    * @param term2oc The occurrence of B in s2.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL, A v B |- sR, tR) as its bottommost sequent.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, s2.root, term1, term2, prinFormula)

    new BinaryTree[Sequent](sequent, s1, s2)
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = OrLeftRuleType
        def aux = ((term1)::Nil)::(term2::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2228:l"
      }
  }

  /** Merges two formulas A & B (marked by term1oc & term2oc in the
    * antecedents of s1 & s2) into a disjunction A Or B.
    * This function merely returns the resulting sequent, not a proof.
    * 
    * @param s1 The left sequent.
    * @param s2 The right sequent.
    * @param term1oc The occurrence of A in s1.
    * @param term2oc The occurrence of B in s2.
    * @return The sequent (sL, tL, A v B |- sR, tR).
    */ 
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, s2, term1, term2, prinFormula)
  }

  /** <pre>Merges two formulas term1 & term2 into a disjunction A Or B.
    * If term1 and/or term2 occur more than once each, only one occurrence
    * of each is merged.
    *
    * Let s1 have (sL, term1 |- sR) as its bottommost sequent and
    * let s2 have (tL, term2 |- tR,) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)             (rest of s2)
    * sL, term1 |- sR        tL, term2 |- tR
    * -------------------------------------- (OrLeft)
    *    sL, tL, term1 v term2 |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with A in the antecedent of its bottommost sequent.
    * @param s2 The right proof with B in the antecedent of its bottommost sequent.
    * @param term1 The left part of the disjunction in s1.
    * @param term2 The right part of the disjunction in s2.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL, term1 v term2 |- sR, tR) as its bottommost sequent.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
    ((s1.root.antecedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
      case ((x::_),(y::_)) => apply(s1, s2, x, y)
      case _ => //throw new LKRuleCreationException("No matching formula occurrences found for application of the rule with the given formula")
                throw new LKUnaryRuleCreationException("or:r", s1, term1::term2::Nil)
    }
  }

  private def getTerms(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    val term2op = s2.antecedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      (term1, term2)
    }
  }

  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula
    val holterm2 = term2.formula
    val form = Or(holterm1, holterm2)
    term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
  }

  private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val ant1 = createContext(s1.antecedent.filterNot(_ == term1))
    val ant2 = createContext(s2.antecedent.filterNot(_ == term2))
    val antecedent = ant1 ++ ant2 :+ prinFormula
    val succedent = createContext(s1.succedent) ++ createContext(s2.succedent)
    Sequent(antecedent, succedent)
  }

  def unapply(proof: LKProof) = if (proof.rule == OrLeftRuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
    }
    else None
}

object OrRight1Rule {
  /** Returns the left subformula.
    * @param main A formula of the form l Or r
    * @return l.
    */
  def computeAux( main: HOLFormula ) = main match { case Or(l, _) => l }

  /** <pre>Replaces a formula F (marked by term1oc) with the disjunction
    * F v term2 in the succcedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    *     sL |- sR, F
    * ------------------- (OrRight1)
    * sL |- sR, F v term2
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, F) as the bottommost sequent.
    * @param term1oc The occurrence of F in the succedent of s1.
    * @param term2 The new term to add.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2: HOLFormula) = {
    val term1 = getTerms(s1.root, term1oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term1, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = OrRight1RuleType
        def aux = ((term1)::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2228:r1"
      }
  }

  /** Replaces a formula F (marked by term1oc) with the disjunction
    * F v term2 in the succedent of a sequent. This function merely
    * returns a sequent, not a proof.
    * 
    * @param s1 The sequent (sL |- sR, F).
    * @param term1oc The occurrence of F in the succedent of s1.
    * @param term2 The new term to add.
    * @return The sequent (sL |- sR, F v term2).
    */
  def apply(s1: Sequent, term1oc: FormulaOccurrence, term2: HOLFormula) = {
    val term1 = getTerms(s1, term1oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term1, prinFormula)
  }

  /** <pre>Replaces a formula term1 with the disjunction
    * term1 v term2 in the succedent of a sequent.
    * If term1 occurs more than once, only one occurrence is replaced.
    * 
    * The rule: 
    *     (rest of s1)
    *   sL |- sR, term1
    * ----------------------- (OrRight1)
    * sL |- sR, term1 v term2
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, term1) as the bottommost sequent.
    * @param term1 The term to be replaced by the new disjunction.
    * @param term2 The new term to add.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    (s1.root.succedent.filter(x => x.formula == term1)).toList match {
      case (x::_) => apply(s1, x, term2)
      case _ => //throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
                throw new LKUnaryRuleCreationException("or:r", s1, term1::term2::Nil)
    }
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxialiary formula is not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      term1
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence, term2: HOLFormula) = {
    val holterm1 = term1.formula
    val form = Or(holterm1, term2)
    term1.factory.createFormulaOccurrence(form, term1::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent)
    val suc1 = createContext(s1.succedent.filterNot(_ == term1))
    val succedent = suc1 :+ prinFormula
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == OrRight1RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object OrRight2Rule {
  /** Returns the right subformula.
    * @param main A formula of the form l Or r
    * @return r.
    */
  def computeAux( main: HOLFormula ) = main match { case Or(_, r) => r }

  /** <pre>Replaces a formula F (marked by term2oc) with the disjunction
    * term1 v F in the succcedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    *     sL |- sR, F
    * ------------------- (OrRight2)
    * sL |- sR, term1 v F
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, F) as the bottommost sequent.
    * @param term1 The new term to add.
    * @param term2oc The occurrence of F in the succedent of s1.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2oc: FormulaOccurrence) = {
    val term2 = getTerms(s1.root, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term2, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = OrRight2RuleType
        def aux = ((term2)::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2228:r2"
      }
  }

  /** Replaces a formula F (marked by term2oc) with the disjunction
    * term1 v F in the succedent of a sequent. This function merely
    * returns a sequent, not a proof.
    * 
    * @param s1 The sequent (sL |- sR, F).
    * @param term1 The new term to add.
    * @param term2oc The occurrence of F in the succedent of s1.
    * @return The sequent (sL |- sR, term1 v F).
    */
  def apply(s1: Sequent, term1: HOLFormula, term2oc: FormulaOccurrence) = {
    val term2 = getTerms(s1, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term2, prinFormula)
  }

  /** <pre>Replaces a formula term2 with the disjunction
    * term1 v term2 in the succedent of a sequent.
    * If term1 occurs more than once, only one occurrence is replaced.
    * 
    * The rule: 
    *     (rest of s1)
    *   sL |- sR, term2
    * ----------------------- (OrRight2)
    * sL |- sR, term1 v term2
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, term2) as the bottommost sequent.
    * @param term1 The new term to add.
    * @param term2 The term to be replaced by the new disjunction.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    (s1.root.succedent.filter(x => x.formula == term2)).toList match {
      case (x::_) => apply(s1, term1, x)
      case _ => //throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
                throw new LKUnaryRuleCreationException("or:r", s1, term1::term2::Nil)
    }
  }
  private def getTerms(s1: Sequent, term2oc: FormulaOccurrence) = {
    val term2op = s1.succedent.find(_ == term2oc)
    if (term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term2 = term2op.get
      term2
    }
  }
  private def getPrinFormula(term1: HOLFormula, term2: FormulaOccurrence) = {
    val holterm2 = term2.formula
    val form = Or(term1, holterm2)
    term2.factory.createFormulaOccurrence(form, term2::Nil)
  }
  private def getSequent(s1: Sequent, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent)
    val suc1 = createContext(s1.succedent.filterNot(_ == term2))
    val succedent = suc1 :+ prinFormula
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == OrRight2RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object ImpLeftRule {
  /** Returns the left subformula.
    * @param main A formula of the form l Imp r
    * @return l.
    */
  def computeLeftAux( main: HOLFormula ) = main match { case Imp(l, _) => l }

  /** Returns the right subformula.
    * @param main A formula of the form l Imp r
    * @return r.
    */
  def computeRightAux( main: HOLFormula ) = main match { case Imp(_, r) => r }


  /** <pre>Introduces an implication A -> B,
    * with A being marked by term1oc in the succedent of s1
    * and with B being marked by term2oc in the antecedent of s2.
    *
    * Let s1 have (sL |- sR, A) as its bottommost sequent and
    * let s2 have (tL, B |- tR) as its bottommost sequent.
    * 
    * The rule: 
    *  (rest of s1)      (rest of s2)
    * sL |- sR, A        tL, B |- tR
    * ------------------------------ (ImpLeft)
    *    sL, tL, A -> B |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with A in the succedent of its bottommost sequent.
    * @param s2: The right proof with B in the antecedent of its bottommost sequent.
    * @param term1oc The occurrence of A in s1.
    * @param term2oc The occurrence of B in s2.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL, A -> B |- sR, tR) as its bottommost sequent.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, s2.root, term1, term2, prinFormula)

    new BinaryTree[Sequent](sequent, s1, s2)
      with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = ImpLeftRuleType
        def aux = (term1::Nil)::(term2::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2283:l"
      }
  }

  /** <pre>Introduces an implication A -> B,
    * with A being marked by term1oc in the succedent of s1
    * and with B being marked by term2oc in the antecedent of s2.
    * This function merely returns the resulting sequent, not a proof.
    *
    * Let s1 have (sL |- sR, A) as its bottommost sequent and
    * let s2 have (tL, B |- tR) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)      (rest of s2)
    * sL |- sR, A        tL, B |- tR
    * ------------------------------ (ImpLeft)
    *    sL, tL, A -> B |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with A in the succedent of its bottommost sequent.
    * @param s2: The right proof with B in the antecedent of its bottommost sequent.
    * @param term1oc The occurrence of A in s1.
    * @param term2oc The occurrence of B in s2.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL, A -> B |- sR, tR) as its bottommost sequent.
    */ 
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, s2, term1, term2, prinFormula)
  }

  /** <pre>Introduces an implication term1 -> term2,
    * with term1 being in the succedent of s1
    * and B being in the antecedent of s2.
    *
    * Let s1 have (sL |- sR, term1) as its bottommost sequent and
    * let s2 have (tL, term2 |- tR) as its bottommost sequent.
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- sR, A        tL, B |- tR
    * ------------------------------ (ImpLeft)
    *    sL, tL, A -> B |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with A in the succedent of its bottommost sequent.
    * @param s2: The right proof with B in the antecedent of its bottommost sequent.
    * @param term1 The formula in s1.
    * @param term2 The formula in s2.
    * @return An LK proof with s1 & s2 as its two subtrees and (sL, tL, term1 -> term2 |- sR, tR) as its bottommost sequent.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
    ((s1.root.succedent.filter(x => x.formula == term1)).toList,(s2.root.antecedent.filter(x => x.formula == term2)).toList) match {
      case ((x::_),(y::_)) => apply(s1, s2, x, y)
      case _ => //throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
                throw new LKBinaryRuleCreationException("impl:l", s1, term1, s2, term2)
    }
  }
  private def getTerms(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    val term2op = s2.antecedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      (term1, term2)
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula
    val holterm2 = term2.formula
    val form = Imp(holterm1, holterm2)
    term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
  }
  private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val ant1 = createContext(s1.antecedent)
    val ant2 = createContext(s2.antecedent.filterNot(_ == term2))
    val antecedent = ant1 ++ ant2 :+ prinFormula
    val suc1 = createContext(s1.succedent.filterNot(_ == term1))
    val suc2 = createContext(s2.succedent)
    val succedent = suc1 ++ suc2
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ImpLeftRuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof1, r.uProof2, r.root, a1, a2, p1))
    }
    else None
}

object ImpRightRule {

  /** <pre>Takes two formulas A & B (marked by term1oc in the antecedent
    * and term2oc in the succedent of s1) and introduces the implication
    * A -> B into the succedent of s1.
    *
    * The rule: 
    *    (rest of s1)
    *   sL, A |- B, sR 
    * -------------------(ImpRight)
    *  sL |- A -> B, sR
    * </pre>
    * 
    * @param s1 The proof with A in the antecedent 
             and B in the succedent of its bottommost sequent.
    * @param term1oc The occurrence of A.
    * @param term2oc The occurrence of B.
    * @return An LK proof with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term1, term2, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = ImpRightRuleType
        def aux = (term1::term2::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u2283:r"
      }
  }

  /** <pre>Takes two formulas A & B (marked by term1oc in the antecedent
    * and term2oc in the succedent of s1) and introduces the implication
    * A -> B into the succedent of s1. This function merely returns
    * the resulting sequent, not a proof
    *
    * The rule: 
    *    (rest of s1)
    *   sL, A |- B, sR 
    * -------------------(ImpRight)
    *  sL |- A -> B, sR
    * </pre>
    * 
    * @param s1 The sequent with A in its antecedent 
             and B in its succedent.
    * @param term1oc The occurrence of A.
    * @param term2oc The occurrence of B.
    * @return The sequent (sL |- A -> B, sR).
    */ 
  def apply(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term1, term2, prinFormula)
  }

  /** <pre>Takes two formulas term1 & term2 from the antecedent and
    * succedent of s1, respectively, and introduces the implication
    * A -> B into the succedent of s1.
    *
    * The rule: 
    *      (rest of s1)
    *  sL, term1 |- term2, sR 
    * -------------------------(ImpRight)
    *  sL |- term1 -> term3, sR
    * </pre>
    * 
    * @param s1 The proof with term1 in the antecedent 
             and term2 in the succedent of its bottommost sequent.
    * @param term1 The formula in the antecedent of s1.
    * @param term2 The formula in the succedent of s1.
    * @return An LK proof with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent.filter(x => x.formula == term1)).toList,(s1.root.succedent.filter(x => x.formula == term2)).toList) match {
      case ((x::_),(y::_)) => apply(s1, x, y)
      case _ => //throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
                throw new LKUnaryRuleCreationException("imp:r", s1, term1::term2::Nil)
    }
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    val term2op = s1.succedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      (term1, term2)
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula
    val holterm2 = term2.formula
    val form = Imp(holterm1, holterm2)
    term1.factory.createFormulaOccurrence(form, term1::term2::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent.filterNot(_ == term1))
    val suc1 = createContext(s1.succedent.filterNot(_ == term2))
    val succedent = suc1 :+ prinFormula
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ImpRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::a2::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, a2, p1))
    }
    else None
}

object NegLeftRule {

  /** Returns the subformula.
    * @param main A formula of the Not l
    * @return l.
    */
  def computeAux( main: HOLFormula ) = main match { case Neg(s) => s }

  /** <pre>Replaces a formula F (marked by term1oc) in the succedent of
    * a sequent  with its negation -F in the antecedent of that sequent. 
    * 
    * The rule: 
    *  (rest of s1)
    *  sL |- F, sR
    * -------------- (NegLeft)
    * sL, -F |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL |- F, sR) as the bottommost sequent.
    * @param term1oc The occurrence of F in the succedent of s1.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence) = {
    val term1 = getTerms(s1.root, term1oc)
    val prinFormula = getPrinFormula(term1)
    val sequent = getSequent(s1.root, term1, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = NegLeftRuleType
        def aux = (term1::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u00ac:l"
      }

  }

  /** Replaces a formula F (marked by term1oc) in the succedent of
    * a sequent  with its negation -F in the antecedent of that sequent. 
    * This function merely returns the resulting sequent, not a proof.
    * 
    * @param s1 The sequent (sL |- F, sR).
    * @param term1oc The occurrence of F in the succedent of s1.
    * @return The sequent (sL, -F |- sR).
    */ 
  def apply(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1 = getTerms(s1, term1oc)
    val prinFormula = getPrinFormula(term1)
    getSequent(s1, term1, prinFormula)
  }

    /** <pre>Replaces a formula term1 in the succedent of a sequent
      * with its negation -term1 in the antecedent of that sequent. 
      * 
      * The rule: 
      *  (rest of s1)
      *  sL |- term1, sR
      * ----------------- (NegLeft)
      * sL, -term1 |- sR
      * </pre>
      * 
      * @param s1 The top proof with (sL |- term1, sR) as the bottommost sequent.
      * @param term1 The formula to negate.
      * @return An LK Proof ending with the new inference.
      */ 
    def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.succedent.filter(x => x.formula == term1)).toList match {
        case (x::_) => apply(s1, x)
        case _ =>
          //throw new LKRuleCreationException("No matching formula occurrences found for application of the rule neg:l with the given formula "
          //  +term1+" in "+s1.root)
          throw new LKUnaryRuleCreationException("neg:l", s1, term1::Nil)
      }
    }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      term1
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence) = {
    val holterm1 = term1.formula
    val form = Neg(holterm1)
    term1.factory.createFormulaOccurrence(form, term1::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent) :+ prinFormula
    val succedent = createContext(s1.succedent.filterNot(_ == term1))
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == NegLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object NegRightRule {

  /** Returns the subformula.
    * @param main A formula of the Not l
    * @return l.
    */
  def computeAux( main: HOLFormula ) = main match { case Neg(s) => s }

  /** <pre>Replaces a formula F (marked by term1oc) in the antecedent of
    * a sequent  with its negation -F in the succedent of that sequent. 
    * 
    * The rule: 
    *  (rest of s1)
    *  sL, F |- sR
    * -------------- (NegLeft)
    * sL |- -F, sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, F |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of F in the antecedent of s1.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence) = {
    val term1 = getTerms(s1.root, term1oc)
    val prinFormula = getPrinFormula(term1)
    val sequent = getSequent(s1.root, term1, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
        def rule = NegRightRuleType
        def aux = (term1::Nil)::Nil
        def prin = prinFormula::Nil
        override def name = "\u00ac:r"
      }

  }

  /** Replaces a formula F (marked by term1oc) in the antecedent of
    * a sequent  with its negation -F in the succedent of that sequent. 
    * This function merely returns the resulting sequent, not a proof.
    * 
    * @param s1 The sequent (sL, F |- sR).
    * @param term1oc The occurrence of F in the anteedent of s1.
    * @return The sequent (sL |- -F, sR).
    */ 
  def apply(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1 = getTerms(s1, term1oc)
    val prinFormula = getPrinFormula(term1)
    getSequent(s1, term1, prinFormula)
  }

    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      (s1.root.antecedent.filter(x => x.formula == term1)).toList match {
        case (x::_) => apply(s1, x)
        case _ =>
          //throw new LKRuleCreationException("No matching formula occurrences found for application of the rule neg:r with the given formula "
          //  +term1+" in "+s1)
          throw new LKUnaryRuleCreationException("neg:r", s1, term1::Nil)
      }
    }

  /** <pre>Replaces a formula term1 in the antecedent of a sequent
    * with its negation -term1 in the succcedent of that sequent. 
    * 
    * The rule: 
    *  (rest of s1)
    *  sL, term1 |- sR
    * ----------------- (NegLeft)
    * sL |- -term1, sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, term1 |- sR) as the bottommost sequent.
    * @param term1oc The formula to negate.
    * @return An LK Proof ending with the new inference.
    */ 
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      term1
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence) = {
    val holterm1 = term1.formula
    val form = Neg(holterm1)
    term1.factory.createFormulaOccurrence(form, term1::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent.filterNot(_ == term1))
    val succedent = createContext(s1.succedent) :+ prinFormula
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == NegRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}
