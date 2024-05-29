package gapt.proofs.lk.util

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.proofs.HOLSequent
import gapt.proofs._
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.provers.Prover
import gapt.provers.escargot.Escargot
import gapt.utils.Tree

class InterpolationException(msg: String) extends Exception(msg)

object ExtractInterpolant {
  def apply(p: LKProof, isPositive: Sequent[Boolean]): Formula =
    Interpolate(p, isPositive)._3

  def apply(p: LKProof, positivePart: Seq[SequentIndex]): Formula =
    Interpolate(p, p.conclusion.indicesSequent.map(positivePart.contains))._3

  def apply(p: LKProof, negativeParts: Tree[SequentIndex]): Tree[Formula] =
    negativeParts.tails.map(neg =>
      apply(p, p.conclusion.indicesSequent.map(!neg.contains(_)))
    )

  /**
   * Given sequents negative: \Gamma |- \Delta and positive: \Pi |- \Lambda,
   * compute a proof of \Gamma, \Pi |- \Delta, \Lambda and from that proof,
   * extract an interpolant I such that \Gamma |- \Delta, I and I, \Pi |- \Lambda
   * are valid.
   */
  def apply(negative: HOLSequent, positive: HOLSequent, prover: Prover = Escargot): Option[Formula] =
    prover.getLKProof(negative ++ positive).map(p =>
      apply(p, for ((f, i) <- p.endSequent.zipWithIndex) yield positive.contains(f, i.polarity))
    )
}

object Interpolate {

  /**
   * This method computes interpolating proofs from propositional LK-proof
   * containing at most atomic cuts. As arguments it expects a proof p
   * and a partition of its end-sequent into two parts:
   * a "negative" part and a "positive" part.
   * For \Gamma |- \Delta being the negative and \Pi |- \Lambda being the
   * positive part, it will compute an interpolant I and proofs of
   * \Gamma |- \Delta, I and I, \Pi |- \Lambda
   *
   * @param p     the LK proof from which the interpolant is to be extracted
   * @param color  indicates which formulas are in the positive part
   * @return      a triple consisting of ( a proof of \Gamma |- \Delta, I,
   *              a proof of I, \Pi |- \Lambda, the FOLFormula I )
   */
  def apply(p: LKProof, color: Sequent[Boolean]): (LKProof, LKProof, Formula) = p match {
    case _ if p.conclusion.sizes != color.sizes =>
      throw new IllegalArgumentException(s"Partition $color has different size than end-sequent:\n${p.conclusion}")

    // axioms

    case LogicalAxiom(atom) =>
      /*
       * Distinguish cases according to the partitions of the formulas in the logical axiom:
       * Case: A :- A and :-   => Interpolant: ⊥   =>   Result: A :- A,⊥ and ⊥ :-
       *
       * Case: :- and A :- A   => Interpolant: ⊤   =>   Result: :- ⊤ and ⊤,A :- A
       *
       * Case: :- A and A :-   => Interpolant: ¬A  =>   Result: :- A,¬A and ¬A,A :-
       *
       * Case: A :- and :- A   => Interpolant: A   =>   Result: A :- A and A :- A
       */
      (color.elements: @unchecked) match {
        case Seq(false, false) => (WeakeningRightRule(p, Bottom()), BottomAxiom, Bottom())
        case Seq(false, true)  => (p, p, atom)
        case Seq(true, false)  => (NegRightRule(p, atom), NegLeftRule(p, atom), -atom)
        case Seq(true, true)   => (TopAxiom, WeakeningLeftRule(p, Top()), Top())
      }

    /*
     * Possible partitions
     *
     * Case: :- ⊤ and :-  => Interpolant: ⊥   =>  Result: :- ⊤,⊥ and ⊥ :-
     *
     * Case: :- and :- ⊤  => Interpolant: ⊤   =>  Result: :- ⊤ and ⊤ :- ⊤
     */
    case TopAxiom =>
      if (!color(Suc(0))) (WeakeningRightRule(p, Bottom()), BottomAxiom, Bottom())
      else (TopAxiom, WeakeningLeftRule(p, Top()), Top())

    /*
     * Possible Partitions:
     *
     * Case: ⊥ :- and :-  => Interpolant: ⊥   =>  Result: ⊥ :- ⊥ and ⊥ :-
     *
     * Case: :- and ⊥ :-  => Interpolant: ⊤   =>  Result: :- ⊤ and ⊤,⊥ :-
     */
    case BottomAxiom =>
      if (!color(Ant(0))) (WeakeningRightRule(p, Bottom()), BottomAxiom, Bottom())
      else (TopAxiom, WeakeningLeftRule(p, Top()), Top())

    /*
     * Possible Partitions:
     *
     * Case: :- s=s and :-  => Interpolant: ⊥   =>  Result: :- s=s,⊥ and ⊥ :-
     *
     * Case: :- and :- s=s  => Interpolant: ⊤   =>  Result: :- ⊤ and ⊤ :- s=s
     */
    case ReflexivityAxiom(term) =>
      if (!color(Suc(0))) (WeakeningRightRule(p, Bottom()), BottomAxiom, Bottom())
      else (TopAxiom, WeakeningLeftRule(p, Top()), Top())

    // structural rules

    case p @ WeakeningLeftRule(subProof, formula) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head)) (WeakeningLeftRule(up_nproof, formula), up_pproof, up_I)
      else (up_nproof, WeakeningLeftRule(up_pproof, formula), up_I)

    case p @ WeakeningRightRule(subProof, formula) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head)) (WeakeningRightRule(up_nproof, formula), up_pproof, up_I)
      else (up_nproof, WeakeningRightRule(up_pproof, formula), up_I)

    case p @ ContractionLeftRule(subProof, aux1, aux2) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))
      val formula = p.mainFormulas.head

      if (!color(p.mainIndices.head)) (ContractionLeftRule(up_nproof, formula), up_pproof, up_I)
      else (up_nproof, ContractionLeftRule(up_pproof, formula), up_I)

    case p @ ContractionRightRule(subProof, aux1, aux2) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))
      val formula = p.mainFormulas.head

      if (!color(p.mainIndices.head)) (ContractionRightRule(up_nproof, formula), up_pproof, up_I)
      else (up_nproof, ContractionRightRule(up_pproof, formula), up_I)

    case p @ CutRule(leftSubProof, aux1, rightSubProof, aux2) =>
      // FIXME: WTF???
      val colorsOfCutFormulaDuplicates = p.conclusion.zip(color).filter(_._1 == p.cutFormula).map(_._2)
      val cutFormulaColor =
        colorsOfCutFormulaDuplicates.contains(true) && !colorsOfCutFormulaDuplicates.contains(false)

      val (up1_nproof, up1_pproof, up1_I) = apply(p.leftSubProof, p.getLeftSequentConnector.parent(color, cutFormulaColor))
      val (up2_nproof, up2_pproof, up2_I) = apply(p.rightSubProof, p.getRightSequentConnector.parent(color, cutFormulaColor))

      if (!cutFormulaColor)
        (
          OrRightRule(CutRule(up1_nproof, up2_nproof, p.cutFormula), up1_I, up2_I),
          OrLeftRule(up1_pproof, up1_I, up2_pproof, up2_I),
          Or(up1_I, up2_I)
        )
      else
        (
          AndRightRule(up1_nproof, up1_I, up2_nproof, up2_I),
          AndLeftRule(CutRule(up1_pproof, up2_pproof, p.cutFormula), up1_I, up2_I),
          And(up1_I, up2_I)
        )

    // propositional rules

    case p @ AndRightRule(leftSubProof, aux1, rightSubProof, aux2) =>
      val (up1_nproof, up1_pproof, up1_I) = apply(p.leftSubProof, p.getLeftSequentConnector.parent(color))
      val (up2_nproof, up2_pproof, up2_I) = apply(p.rightSubProof, p.getRightSequentConnector.parent(color))

      if (!color(p.mainIndices.head))
        (
          OrRightRule(AndRightRule(up1_nproof, p.leftConjunct, up2_nproof, p.rightConjunct), up1_I, up2_I),
          OrLeftRule(up1_pproof, up1_I, up2_pproof, up2_I),
          Or(up1_I, up2_I)
        )
      else
        (
          AndRightRule(up1_nproof, up1_I, up2_nproof, up2_I),
          AndLeftRule(AndRightRule(up1_pproof, p.leftConjunct, up2_pproof, p.rightConjunct), up1_I, up2_I),
          And(up1_I, up2_I)
        )

    case p @ AndLeftRule(subProof, aux1, aux2) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head)) (AndLeftRule(up_nproof, p.leftConjunct, p.rightConjunct), up_pproof, up_I)
      else (up_nproof, AndLeftRule(up_pproof, p.leftConjunct, p.rightConjunct), up_I)

    case p @ OrLeftRule(leftSubProof, aux1, rightSubProof, aux2) =>
      val (up1_nproof, up1_pproof, up1_I) = apply(p.leftSubProof, p.getLeftSequentConnector.parent(color))
      val (up2_nproof, up2_pproof, up2_I) = apply(p.rightSubProof, p.getRightSequentConnector.parent(color))

      if (!color(p.mainIndices.head))
        (
          OrRightRule(OrLeftRule(up1_nproof, p.leftDisjunct, up2_nproof, p.rightDisjunct), up1_I, up2_I),
          OrLeftRule(up1_pproof, up1_I, up2_pproof, up2_I),
          Or(up1_I, up2_I)
        )
      else
        (
          AndRightRule(up1_nproof, up1_I, up2_nproof, up2_I),
          AndLeftRule(OrLeftRule(up1_pproof, p.leftDisjunct, up2_pproof, p.rightDisjunct), up1_I, up2_I),
          And(up1_I, up2_I)
        )

    case p @ OrRightRule(subProof, aux1, aux2) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))
      val formula1 = p.leftDisjunct
      val formula2 = p.rightDisjunct

      if (!color(p.mainIndices.head)) (OrRightRule(up_nproof, formula1, formula2), up_pproof, up_I)
      else (up_nproof, OrRightRule(up_pproof, formula1, formula2), up_I)

    case p @ NegLeftRule(subProof, aux) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head)) (NegLeftRule(up_nproof, subProof.endSequent(aux)), up_pproof, up_I)
      else (up_nproof, NegLeftRule(up_pproof, subProof.endSequent(aux)), up_I)

    case p @ NegRightRule(subProof, aux) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head)) (NegRightRule(up_nproof, subProof.endSequent(aux)), up_pproof, up_I)
      else (up_nproof, NegRightRule(up_pproof, subProof.endSequent(aux)), up_I)

    case p @ ImpLeftRule(leftSubProof, aux1, rightSubProof, aux2) =>
      val (up1_nproof, up1_pproof, up1_I) = apply(p.leftSubProof, p.getLeftSequentConnector.parent(color))
      val (up2_nproof, up2_pproof, up2_I) = apply(p.rightSubProof, p.getRightSequentConnector.parent(color))

      if (!color(p.mainIndices.head))
        (
          OrRightRule(ImpLeftRule(up1_nproof, p.impPremise, up2_nproof, p.impConclusion), up1_I, up2_I),
          OrLeftRule(up1_pproof, up1_I, up2_pproof, up2_I),
          Or(up1_I, up2_I)
        )
      else
        (
          AndRightRule(up1_nproof, up1_I, up2_nproof, up2_I),
          AndLeftRule(ImpLeftRule(up1_pproof, p.impPremise, up2_pproof, p.impConclusion), up1_I, up2_I),
          And(up1_I, up2_I)
        )

    case p @ ImpRightRule(subProof, aux1, aux2) =>
      val (up_nproof, up_pproof, up_I) = apply(p.subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head)) (ImpRightRule(up_nproof, p.impPremise, p.impConclusion), up_pproof, up_I)
      else (up_nproof, ImpRightRule(up_pproof, p.impPremise, p.impConclusion), up_I)

    // equality rules

    case p @ EqualityRightRule(subProof, eq, aux, con) =>
      val (up_nproof, up_pproof, up_I) = apply(
        p.subProof,
        p.getSequentConnector.parent(color).updated(eq, color(p.eqInConclusion)).updated(aux, color(p.auxInConclusion))
      )

      (color(p.eqInConclusion), color(p.mainIndices.head)) match {
        case (false, false) => (EqualityRightRule(up_nproof, eq, p.auxFormula, con), up_pproof, up_I)
        case (true, true)   => (up_nproof, EqualityRightRule(up_pproof, eq, p.auxFormula, con), up_I)
        case (true, false) =>
          val ipl = Imp(p.equation, up_I)

          val up_nproof1 = WeakeningLeftRule(up_nproof, p.equation)
          val up_nproof2 = EqualityRightRule(up_nproof1, eq, p.auxFormula, con)
          val up_nproof3 = ImpRightRule(up_nproof2, p.equation, up_I)

          val up_pproof1 = ImpLeftRule(LogicalAxiom(p.equation), p.equation, up_pproof, up_I)
          val up_pproof2 = ContractionLeftRule(up_pproof1, p.equation)

          (up_nproof3, up_pproof2, ipl)
        case (false, true) =>
          val ipl = And(p.equation, up_I)

          val up_nproof1 = AndRightRule(LogicalAxiom(p.equation), up_nproof, And(p.equation, up_I))
          val up_nproof2 = ContractionLeftRule(up_nproof1, p.equation)

          val up_pproof1 = WeakeningLeftRule(up_pproof, p.equation)
          val up_pproof2 = EqualityRightRule(up_pproof1, eq, p.auxFormula, con)
          val up_pproof3 = AndLeftRule(up_pproof2, p.equation, up_I)

          (up_nproof2, up_pproof3, ipl)
      }

    case p @ EqualityLeftRule(subProof, eq, aux, con) =>
      val (up_nproof, up_pproof, up_I) = apply(
        p.subProof,
        p.getSequentConnector.parent(color).updated(eq, color(p.eqInConclusion)).updated(aux, color(p.auxInConclusion))
      )
      var ipl = up_I

      (color(p.eqInConclusion), color(p.mainIndices.head)) match {
        case (false, false) => (EqualityLeftRule(up_nproof, eq, p.auxFormula, con), up_pproof, up_I)
        case (true, true)   => (up_nproof, EqualityLeftRule(up_pproof, eq, p.auxFormula, con), up_I)
        case (true, false) =>
          ipl = Imp(p.equation, up_I)

          val up_nproof1 = WeakeningLeftRule(up_nproof, p.equation)
          val up_nproof2 = EqualityLeftRule(up_nproof1, eq, p.auxFormula, con)
          val up_nproof3 = ImpRightRule(up_nproof2, p.equation, up_I)

          val up_pproof1 = ImpLeftRule(LogicalAxiom(p.equation), p.equation, up_pproof, up_I)
          val up_pproof2 = ContractionLeftRule(up_pproof1, p.equation)

          (up_nproof3, up_pproof2, ipl)
        case (false, true) =>
          ipl = And(p.equation, up_I)

          val up_nproof1 = AndRightRule(LogicalAxiom(p.equation), up_nproof, And(p.equation, up_I))
          val up_nproof2 = ContractionLeftRule(up_nproof1, p.equation)

          val up_pproof1 = WeakeningLeftRule(up_pproof, p.equation)
          val up_pproof2 = EqualityLeftRule(up_pproof1, eq, p.auxFormula, con)
          val up_pproof3 = AndLeftRule(up_pproof2, p.equation, up_I)

          (up_nproof2, up_pproof3, ipl)
      }

    case p @ ForallLeftRule(subProof, aux, main, term, quantVar) =>
      val (nproof, pproof, interpolant) = apply(subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head))
        (ForallLeftRule(nproof, p.mainFormula, term), pproof, interpolant)
      else
        (nproof, ForallLeftRule(pproof, p.mainFormula, term), interpolant)

    case p @ ExistsRightRule(subProof, aux, main, term, quantVar) =>
      val (nproof, pproof, interpolant) = apply(subProof, p.getSequentConnector.parent(color))

      if (!color(p.mainIndices.head))
        (ExistsRightRule(nproof, p.mainFormula, term), pproof, interpolant)
      else
        (nproof, ExistsRightRule(pproof, p.mainFormula, term), interpolant)
  }

}
