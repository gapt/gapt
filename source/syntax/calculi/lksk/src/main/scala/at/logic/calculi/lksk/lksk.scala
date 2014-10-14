/*
 * lksk.scala
 *
 */

package at.logic.calculi.lksk

import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.trees._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.{InitialRuleType, WeakeningLeftRuleType, WeakeningRightRuleType, Axiom => LKAxiom, _}
import TypeSynonyms._

// lksk proofs
// rules are extracted in the form (UpperSequent(s), LowerSequent, AuxialiaryFormula(s), PrincipalFormula(s))

// actual rule extractor/factories
// Axioms (and weakenings) always return a pair(Proof, mapping) which maps the indices of the list given into the new occurrences.
object Axiom {
  /**
   * Creates an LKSK Axiom rule from the given unlabeled sequent a pair of labels
   * @param seq unlabeled sequent of the axiom
   * @param maps pair of lists with labels for the antecedent and succedent
   * @return an LKProof of the Axiom
   */
  def apply(seq: FSequent, maps: (List[Label], List[Label])) : LKProof = createDefault(seq, maps)._1

  def createDefault(seq: FSequent, maps: (List[Label], List[Label])): (LKProof, (List[LabelledFormulaOccurrence],List[LabelledFormulaOccurrence])) = {
    val left: Seq[LabelledFormulaOccurrence] =
      seq._1.zip(maps._1).map( p => createOccurrence( p._1 , p._2 ) )
    val right: Seq[LabelledFormulaOccurrence] =
      seq._2.zip(maps._2).map( p => createOccurrence( p._1, p._2 ) )
    // I think we want LeafTree[LabelledSequent] here, but it's incompatible with LKProof
    (new LeafTree[Sequent](new LabelledSequent(left, right ) ) with NullaryLKProof {def rule = InitialRuleType}, (left.toList,right.toList))
  }
  def createOccurrence(f: HOLFormula, l: Label): LabelledFormulaOccurrence =
    LKskFOFactory.createInitialOccurrence(f, l)
  def unapply(proof: LKProof) = if (proof.rule == InitialRuleType) Some((proof.root)) else None
}

object WeakeningLeftRule {
  /**
   * Creates a rule weakening in the given formula and label
   * @param s1 the parent proof
   * @param f the formula weakened in
   * @param l the label
   * @return an LKProof with last rule weakening left
   */
  def apply(s1: LKProof, f: HOLFormula, l: Label) = createDefault(s1, f, l)

  def createDefault(s1: LKProof, f: HOLFormula, l: Label) = {
    val prinFormula : LabelledFormulaOccurrence = LKskFOFactory.createInitialOccurrence(f, l)
    // I think we want LeafTree[LabelledSequent] here, but it's incompatible with LKProof
    new UnaryTree[Sequent](
      new LabelledSequent( createContext(s1.root.antecedent).asInstanceOf[Seq[LabelledFormulaOccurrence]] :+ prinFormula, createContext(s1.root.succedent).asInstanceOf[Seq[LabelledFormulaOccurrence]]), s1)
      with UnaryLKProof with PrincipalFormulas {
        def rule = WeakeningLeftRuleType
        def prin = prinFormula::Nil
        override def name = "w:l (sk)"
      }
  }
  def unapply(proof: LKProof) = if (proof.rule == WeakeningLeftRuleType && proof.root.isInstanceOf[LabelledSequent]) {
      val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, p1.asInstanceOf[LabelledFormulaOccurrence]))
    }
    else None
}

object WeakeningRightRule {
  /**
   * Creates a rule weakening in the given formula and label
   * @param s1 the parent proof
   * @param f the formula weakened in
   * @param l the label
   * @return an LKProof with last rule weakening left
   */
  def apply(s1: LKProof, f: HOLFormula, l : Label) : LKProof = createDefault(s1, f, l)

  def createDefault(s1: LKProof, f: HOLFormula, l: Label) = {
    val prinFormula = LKskFOFactory.createInitialOccurrence(f, l)
    new UnaryTree[Sequent](
      new LabelledSequent(createContext(s1.root.antecedent).asInstanceOf[Seq[LabelledFormulaOccurrence]], createContext(s1.root.succedent).asInstanceOf[Seq[LabelledFormulaOccurrence]] :+ prinFormula), s1)
      with UnaryLKProof with PrincipalFormulas {
        def rule = WeakeningRightRuleType
        def prin = prinFormula::Nil
        override def name = "w:r (sk)"
      }
  }
  def unapply(proof: LKProof) = if (proof.rule == WeakeningRightRuleType && proof.root.isInstanceOf[LabelledSequent]) {
      val r = proof.asInstanceOf[UnaryLKProof with PrincipalFormulas]
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root.asInstanceOf[LabelledSequent], p1.asInstanceOf[LabelledFormulaOccurrence]))
    }
    else None
}

// Quanitifier rules
case object ForallSkLeftRuleType extends UnaryRuleTypeA
case object ForallSkRightRuleType extends UnaryRuleTypeA
case object ExistsSkLeftRuleType extends UnaryRuleTypeA
case object ExistsSkRightRuleType extends UnaryRuleTypeA

// def createWeakQuantMain(formula: Formula, ancestor: LabelledFormulaOccurrence, term: Option[LambdaExpression])

object ForallSkLeftRule {
  // removeFromLabel indicates whether to remove the term subst from the label of the main formula.
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: HOLFormula, subst_t: HOLExpression, removeFromLabel: Boolean) = {
    main match {
      case AllVar( x, sub) => {
        // TODO: comment in to check validity of the rule.
        // commented out at the moment because we don't know the subst term
        // in the XML parser. We need first-order unification for that.
        //assert( betaNormalize( App( sub, subst_t ) ) == aux ) //needs to change because we changed the All matchen to AllVar
        if ( !s1.root.antecedent.contains( auxf ) )
          throw new LKUnaryRuleCreationException("Premise does not contain the given formula occurrence.", s1, auxf.formula::Nil)
        if ( !auxf.skolem_label.contains( subst_t ) )
          throw new LKUnaryRuleCreationException("Auxiliary formula occurrence label of ForallSkLeftRule does not contain substitution term. Label: " + auxf.skolem_label.toString + ", substitution term: " + subst_t.toString, s1, auxf.formula::Nil)
        val prinFormula = 
          LKskFOFactory.createWeakQuantMain(main, auxf, if (removeFromLabel) Some(subst_t) else None)
        new UnaryTree[Sequent](
          new LabelledSequent(createContext((s1.root.antecedent.filterNot(_ == auxf))).asInstanceOf[Seq[LabelledFormulaOccurrence]] :+ prinFormula, createContext((s1.root.succedent)).asInstanceOf[Seq[LabelledFormulaOccurrence]]), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = ForallSkLeftRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = subst_t
            override def name = "\u2200:l (sk)"
          }
      }
      case _ => throw new LKUnaryRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.", s1, List(auxf.formula))
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ForallSkLeftRuleType) {
      //println("ForallSkLeftRule Unapply")
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root.asInstanceOf[LabelledSequent], a1.asInstanceOf[LabelledFormulaOccurrence], p1.asInstanceOf[LabelledFormulaOccurrence], r.subst))
    }
    else None
}

object ExistsSkRightRule {
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: HOLFormula, subst_t: HOLExpression, removeFromLabel: Boolean) = {
    main match {
      case ExVar( x, sub ) => {
        //assert( betaNormalize( App( sub, subst_t ) ) == aux ) //needs to change because we changed the All matchen to AllVar
        if ( !s1.root.succedent.contains( auxf ) )
          throw new LKUnaryRuleCreationException("Premise does not contain the given formula occurrence.", s1, auxf.formula::Nil)
        if ( !auxf.skolem_label.contains( subst_t ) )
          throw new LKUnaryRuleCreationException("Auxiliary formula occurrence label of ExistsSkLeftRule does not contain substitution term.", s1, auxf.formula::Nil)
        val prinFormula = 
          LKskFOFactory.createWeakQuantMain(main, auxf, if (removeFromLabel) Some(subst_t) else None)
        new UnaryTree[Sequent](
          new LabelledSequent(createContext(s1.root.antecedent).asInstanceOf[Seq[LabelledFormulaOccurrence]], createContext((s1.root.succedent.filterNot(_ == auxf))).asInstanceOf[Seq[LabelledFormulaOccurrence]] :+ prinFormula), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = ExistsSkRightRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = subst_t
            override def name = "\u2203:r (sk)"
          }
      }
      case _ => throw new LKUnaryRuleCreationException("Main formula of ExistsSkRightRule must have a universal quantifier as head symbol.", s1, List(auxf.formula))
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ExistsSkRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root.asInstanceOf[LabelledSequent], a1.asInstanceOf[LabelledFormulaOccurrence], p1.asInstanceOf[LabelledFormulaOccurrence], r.subst))
    }
    else None
}

object ForallSkRightRule {
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: HOLFormula, skolem_term: HOLExpression) = {
    main match {
      case AllVar( x, sub ) => {
        // TODO: check Skolem term
        if (!s1.root.succedent.contains( auxf ) )
          throw new LKUnaryRuleCreationException("Premise does not contain the given formula occurrence.", s1, auxf.formula::Nil)
        val prinFormula = auxf.factory.createFormulaOccurrence(main, auxf::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryTree[Sequent](
          new LabelledSequent(createContext(s1.root.antecedent).asInstanceOf[Seq[LabelledFormulaOccurrence]],
                              createContext(s1.root.succedent.filterNot(_ == auxf)).asInstanceOf[Seq[LabelledFormulaOccurrence]] :+ prinFormula), s1)
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = ForallSkRightRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = skolem_term
            override def name = "\u2200:r (sk)"
          }
        }
      case _ => throw new LKUnaryRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.", s1, auxf.formula::Nil)
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ForallSkRightRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root.asInstanceOf[LabelledSequent], a1.asInstanceOf[LabelledFormulaOccurrence], p1.asInstanceOf[LabelledFormulaOccurrence], r.subst))
    }
    else None
}

object ExistsSkLeftRule {
  def apply(s1: LKProof, auxf: LabelledFormulaOccurrence, main: HOLFormula, skolem_term: HOLExpression) = {
    main match {
      case ExVar( x, sub) => {
        // TODO: check Skolem term
        if (!s1.root.antecedent.contains( auxf ) )
          throw new LKUnaryRuleCreationException("Premise does not contain the given formula occurrence.", s1, auxf.formula::Nil)
        val prinFormula = auxf.factory.createFormulaOccurrence(main, auxf::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryTree[Sequent](
          new LabelledSequent(createContext((s1.root.antecedent.filterNot( _ == auxf))).asInstanceOf[Seq[LabelledFormulaOccurrence]] :+ prinFormula, createContext((s1.root.succedent)).asInstanceOf[Seq[LabelledFormulaOccurrence]]), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = ExistsSkLeftRuleType
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = skolem_term
            override def name = "\u2203:l (sk)"
          }
        }
      case _ => throw new LKUnaryRuleCreationException("Main formula of ForallLeftRule must have a universal quantifier as head symbol.", s1, auxf.formula::Nil)
    }
  }

  def unapply(proof: LKProof) = if (proof.rule == ExistsSkLeftRuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root.asInstanceOf[LabelledSequent], a1.asInstanceOf[LabelledFormulaOccurrence], p1.asInstanceOf[LabelledFormulaOccurrence], r.subst))
    }
    else None
}


