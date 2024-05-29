package gapt.proofs.ceres

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.util.freeVariables
import gapt.expr.util.variables
import gapt.proofs._
import gapt.proofs.ceres.Pickrule._
import gapt.proofs.lk._
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.WeakeningMacroRule
import gapt.utils.NameGenerator

object SingleProjectionWithQuantifiers {

  // This method computes the standard projections according to the original CERES definition.
  def apply(proof: LKProof): LKProof =
    apply(proof, proof.endSequent.map(_ => false), _ => true)._2

  private def apply(proof: LKProof, pred: Formula => Boolean): LKProof =
    apply(proof, proof.endSequent.map(_ => false), pred)._2

  private def apply(proof: LKProof, cut_ancs: Sequent[Boolean], pred: Formula => Boolean): (Option[SequentIndex], LKProof) = {
    apply_(proof, cut_ancs, pred)
  }

  private def apply_(proof: LKProof, cut_ancs: Sequent[Boolean], pred: Formula => Boolean): (Option[SequentIndex], LKProof) = {
    implicit val c_ancs: Sequent[Boolean] = cut_ancs
    // proof.occConnectors

    proof match {
      /* Structural rules except cut */
      case InitialSequent(p) =>
        val stepOne = p.antecedent.zip(cut_ancs.antecedent).foldLeft((proof, (cut_ancs, List[Formula]()))) { (update, pp) =>
          if (pp._2) {
            val up = NegRightRule(update._1, pp._1)
            val new_cut_ancs = update._2._1.delete(p.indexOfInAnt(pp._1)).insertAt(up.endSequent.indexOfInSuc(up.mainFormula), true)
            (up, (new_cut_ancs, update._2._2.:+(up.mainFormula)))
          } else update
        }
        val stepTwo = stepOne._1.endSequent.succedent.zip(stepOne._2._1.succedent).foldLeft(stepOne._2._2)((cuts, pair) =>
          if (pair._2 && !stepOne._2._2.contains(pair._1)) cuts.:+(pair._1)
          else cuts
        )
        if (stepTwo.nonEmpty) {
          val stepThree = stepTwo.tail.foldLeft((stepOne._1, stepTwo.head)) { (cf, i) =>
            val update = OrRightRule(cf._1, cf._1.endSequent.indexOfInSuc(cf._2), cf._1.endSequent.indexOfInSuc(i))
            (update, update.mainFormula)
          }
          (Some(stepThree._1.endSequent.indexOfInSuc(stepThree._2)), stepThree._1)
        } else (None, proof)

      case ContractionLeftRule(p, a1, a2)  => handleContractionRule(proof, p, a1, a2, ContractionLeftRule.apply, pred)
      case ContractionRightRule(p, a1, a2) => handleContractionRule(proof, p, a1, a2, ContractionRightRule.apply, pred)
      case WeakeningLeftRule(p, m)         => handleWeakeningRule(proof, p, m, WeakeningLeftRule.apply, pred)
      case WeakeningRightRule(p, m)        => handleWeakeningRule(proof, p, m, WeakeningRightRule.apply, pred)

      /* Logical rules */
      case AndRightRule(p1, a1, p2, a2) => handleBinaryRule(proof, p1, p2, a1, a2, AndRightRule.apply, pred)
      case OrLeftRule(p1, a1, p2, a2)   => handleBinaryRule(proof, p1, p2, a1, a2, OrLeftRule.apply, pred)
      case ImpLeftRule(p1, a1, p2, a2)  => handleBinaryRule(proof, p1, p2, a1, a2, ImpLeftRule.apply, pred)
      case NegLeftRule(p, a)            => handleNegRule(proof, p, a, NegLeftRule.apply, pred)
      case NegRightRule(p, a)           => handleNegRule(proof, p, a, NegRightRule.apply, pred)
      case OrRightRule(p, a1, a2)       => handleUnaryRule(proof, p, a1, a2, OrRightRule.apply, pred)
      case AndLeftRule(p, a1, a2)       => handleUnaryRule(proof, p, a1, a2, AndLeftRule.apply, pred)
      case ImpRightRule(p, a1, a2)      => handleUnaryRule(proof, p, a1, a2, ImpRightRule.apply, pred)

      /* quantifier rules  */
      case ForallRightRule(p, _, _, _)    => handleStrongQuantRule(proof, p, ForallRightRule.apply, pred)
      case ExistsLeftRule(p, _, _, _)     => handleStrongQuantRule(proof, p, ExistsLeftRule.apply, pred)
      case ForallLeftRule(p, a, f, t, v)  => handleWeakQuantRule(proof, p, a, f, t, v, ForallLeftRule.apply, pred)
      case ExistsRightRule(p, a, f, t, v) => handleWeakQuantRule(proof, p, a, f, t, v, ExistsRightRule.apply, pred)
      case ForallSkRightRule(p, a, m, t)  => handleSkQuantRule(proof, p, a, m, t, ForallSkRightRule.apply, pred)
      case ExistsSkLeftRule(p, a, m, t)   => handleSkQuantRule(proof, p, a, m, t, ExistsSkLeftRule.apply, pred)

      case ConversionLeftRule(p, a, m)      => handleDefRule(proof, p, a, m, ConversionLeftRule.apply, pred)
      case ConversionRightRule(p, a, m)     => handleDefRule(proof, p, a, m, ConversionRightRule.apply, pred)
      case EqualityLeftRule(p1, e, a, con)  => handleEqRule(proof, p1, e, a, con, EqualityLeftRule.apply, pred)
      case EqualityRightRule(p1, e, a, con) => handleEqRule(proof, p1, e, a, con, EqualityRightRule.apply, pred)
      case rule @ CutRule(p1, a1, p2, a2) =>
        if (pred(rule.cutFormula)) {
          /* this cut is taken into account */
          val new_cut_ancs_left = mapToUpperProof(proof.occConnectors.head, cut_ancs, default = true)
          val new_cut_ancs_right = mapToUpperProof(proof.occConnectors(1), cut_ancs, default = true)
          require(new_cut_ancs_left.size == p1.endSequent.size, "Cut ancestor information does not fit to end-sequent!")
          require(new_cut_ancs_right.size == p2.endSequent.size, "Cut ancestor information does not fit to end-sequent!")
          val s1 = apply(p1, new_cut_ancs_left, pred)
          val s2 = apply(p2, new_cut_ancs_right, pred)
          handleBinaryCutAnc(s1, s2)
        } else {
          /* this cut is skipped */
          val new_cut_ancs_left = mapToUpperProof(proof.occConnectors.head, cut_ancs, default = false)
          val new_cut_ancs_right = mapToUpperProof(proof.occConnectors(1), cut_ancs, default = false)
          require(new_cut_ancs_left.size == p1.endSequent.size, "Cut ancestor information does not fit to end-sequent!")
          require(new_cut_ancs_right.size == p2.endSequent.size, "Cut ancestor information does not fit to end-sequent!")
          val s1 = apply(p1, new_cut_ancs_left, pred)
          val s2 = apply(p2, new_cut_ancs_right, pred)
          require(p1.conclusion(a1) == p2.conclusion(a2), "Original cut formulas must be equal!")

          val form1: Option[Formula] =
            if (s1._1.nonEmpty)
              Some(s1._2.endSequent(s1._1.get))
            else None
          val form2: Option[Formula] =
            if (s2._1.nonEmpty)
              Some(s2._2.endSequent(s1._1.get))
            else None
          val List(aux1, aux2) = pickrule(proof, List(p1, p2), List(s1._2, s2._2), List(a1, a2))
          require(s1._2.conclusion(aux1) == s2._2.conclusion(aux2), "New cut formulas must be equal!")
          val preProof = CutRule(s1._2, aux1, s2._2, aux2)
          if (form1.nonEmpty)
            if (form2.nonEmpty) {
              val finproof = OrRightRule(preProof, preProof.endSequent.indexOfInSuc(form1.get), preProof.endSequent.indexOfInSuc(form2.get))
              (Some(finproof.endSequent.indexOfInSuc(finproof.mainFormula)), finproof)
            } else (Some(preProof.endSequent.indexOfInSuc(form1.get)), preProof)
          else if (form2.nonEmpty) (Some(preProof.endSequent.indexOfInSuc(form2.get)), preProof)
          else (None, preProof)
        }
    }
  }

  /* finds the cut ancestor sequent in the parent connected with the occurrence connector */
  private def copySetToAncestor(connector: SequentConnector, s: Sequent[Boolean]): Sequent[Boolean] = {
    connector.parents(s).map(_.head)
  }

  /* traces the ancestor relationship to infer cut-formulas in the parent proof. if a formula does not have parents,
     use default */
  private def mapToUpperProof[Formula](conn: SequentConnector, cut_occs: Sequent[Boolean], default: Boolean) =
    conn.parents(cut_occs).map(_.headOption getOrElse default)

  private def handleBinaryESAnc(proof: LKProof, parent1: LKProof, parent2: LKProof, s1: (Option[SequentIndex], LKProof), s2: (Option[SequentIndex], LKProof), constructor: (LKProof, SequentIndex, LKProof, SequentIndex) => LKProof): (Option[SequentIndex], LKProof) = {

    val form1: Option[Formula] =
      if (s1._1.nonEmpty)
        Some(s1._2.endSequent(s1._1.get))
      else None
    val form2: Option[Formula] =
      if (s2._1.nonEmpty)
        Some(s2._2.endSequent(s1._1.get))
      else None
    val List(a1, a2) = pickrule(proof, List(parent1, parent2), List(s1._2, s2._2), List(proof.auxIndices.head.head, proof.auxIndices(1).head))
    val preProof = constructor(s1._2, a1, s2._2, a2)
    if (form1.nonEmpty)
      if (form2.nonEmpty) {
        val finproof = OrRightRule(preProof, preProof.endSequent.indexOfInSuc(form1.get), preProof.endSequent.indexOfInSuc(form2.get))
        (Some(finproof.endSequent.indexOfInSuc(finproof.mainFormula)), finproof)
      } else (Some(preProof.endSequent.indexOfInSuc(form1.get)), preProof)
    else if (form2.nonEmpty) (Some(preProof.endSequent.indexOfInSuc(form2.get)), preProof)
    else (None, preProof)
  }

  private def getESAncs(proof: LKProof, cut_ancs: Sequent[Boolean]): HOLSequent =
    // use cut_ancs as characteristic function to filter the the cut-ancestors from the current sequent
    (proof.endSequent zip cut_ancs).filterNot(_._2).map(_._1)

  // Handles the case of a binary rule operating on a cut-ancestor.
  private def handleBinaryCutAnc(
      s1: (Option[SequentIndex], LKProof),
      s2: (Option[SequentIndex], LKProof)
  ): (Option[SequentIndex], LKProof) = {
    if (s1._1.nonEmpty) {
      if (s2._1.nonEmpty) {
        val Ng = new NameGenerator(s1._2.endSequent.succedent.map(x => variables(x).map(x => x.name)).flatten ++
          s1._2.endSequent.antecedent.map(x => variables(x).map(x => x.name)).flatten ++
          s2._2.endSequent.succedent.map(x => variables(x).map(x => x.name)).flatten ++
          s2._2.endSequent.antecedent.map(x => variables(x).map(x => x.name)).flatten)
        val eNg = new ExprNameGenerator(Ng)
        val (pL, posL) =
          if (freeVariables(s1._2.endSequent(s1._1.get)).nonEmpty)
            freeVariables(s1._2.endSequent(s1._1.get)).foldLeft((s1._2, s1._1.get))((preProof, curvar) => {
              val qproof = ForallRightRule(preProof._1, preProof._2, curvar, eNg.fresh(curvar))
              (qproof, qproof.mainIndices.head)
            })
          else (s1._2, s1._1.get)

        val (pR, posR) =
          if (freeVariables(s2._2.endSequent(s2._1.get)).nonEmpty)
            freeVariables(s2._2.endSequent(s2._1.get)).foldLeft((s2._2, s2._1.get))((preProof, curvar) => {
              val qproof = ForallRightRule(preProof._1, preProof._2, curvar, eNg.fresh(curvar))
              (qproof, qproof.mainIndices.head)
            })
          else (s2._2, s2._1.get)

        val proof = AndRightRule(pL, pL.endSequent(posL), pR, pR.endSequent(posR))
        (Some(proof.endSequent.indexOfInSuc(proof.mainFormula)), proof)
      } else {
        val antlist = s1._2.endSequent.antecedent.toSet.diff(s2._2.endSequent.antecedent.toSet)
        val suclist = s1._2.endSequent.succedent.toSet.diff(s2._2.endSequent.succedent.toSet)
        val proof = WeakeningMacroRule(s1._2, antlist.toSeq, suclist.toSeq)
        (Some(s1._2.endSequent.indexOfInSuc(s1._2.endSequent(s1._1.get))), proof)
      }
    } else {
      val antlist = s2._2.endSequent.antecedent.toSet.diff(s1._2.endSequent.antecedent.toSet)
      val suclist = s2._2.endSequent.succedent.toSet.diff(s1._2.endSequent.succedent.toSet)
      val proof = WeakeningMacroRule(s2._2, antlist.toSeq, suclist.toSeq)
      (Some(s2._2.endSequent.indexOfInSuc(s2._2.endSequent(s2._1.get))), proof)
    }

  }

  def handleContractionRule(
      proof: LKProof,
      p: LKProof,
      a1: SequentIndex,
      a2: SequentIndex,
      constructor: (LKProof, SequentIndex, SequentIndex) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else {
      val List(a1_, a2_) = pickrule(proof, List(p), List(s._2), List(a1, a2))
      val finproof = constructor(s._2, a1_, a2_)
      if (s._1.nonEmpty) {
        val form = s._2.endSequent(s._1.get)
        (Some(finproof.endSequent.indexOfInSuc(form)), finproof)
      } else (None, finproof)
    }
  }

  // implication does not weaken the second argument, we need two occs
  private def handleUnaryRule[T](
      proof: LKProof,
      p: LKProof,
      a1: SequentIndex,
      a2: SequentIndex,
      constructor: (LKProof, SequentIndex, SequentIndex) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else {
      val List(a1_, a2_) = pickrule(proof, List(p), List(s._2), List(a1, a2))
      val finproof = constructor(s._2, a1_, a2_)
      if (s._1.nonEmpty) {
        val form = s._2.endSequent(s._1.get)
        (Some(finproof.endSequent.indexOfInSuc(form)), finproof)
      } else (None, finproof)
    }
  }

  private def handleWeakeningRule(
      proof: LKProof,
      p: LKProof,
      m: Formula,
      constructor: (LKProof, Formula) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else {
      val finproof = constructor(s._2, m)
      if (s._1.nonEmpty) {
        val form = s._2.endSequent(s._1.get)
        (Some(finproof.endSequent.indexOfInSuc(form)), finproof)
      } else (None, finproof)
    }
  }

  private def handleDefRule(
      proof: LKProof,
      p: LKProof,
      a: SequentIndex,
      m: Formula,
      constructor: (LKProof, SequentIndex, Formula) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else {
      val List(a_) = pickrule(proof, List(p), List(s._2), List(a))
      val finproof = constructor(s._2, a_, m)
      if (s._1.nonEmpty) {
        val form = s._2.endSequent(s._1.get)
        (Some(finproof.endSequent.indexOfInSuc(form)), finproof)
      } else (None, finproof)
    }
  }

  private def handleNegRule(
      proof: LKProof,
      p: LKProof,
      a: SequentIndex,
      constructor: (LKProof, SequentIndex) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else {
      val List(a_) = pickrule(proof, List(p), List(s._2), List(a))
      val finproof = constructor(s._2, a_)
      if (s._1.nonEmpty) {
        val form = s._2.endSequent(s._1.get)
        (Some(finproof.endSequent.indexOfInSuc(form)), finproof)
      } else (None, finproof)
    }
  }

  private def handleWeakQuantRule(
      proof: LKProof,
      p: LKProof,
      a: SequentIndex,
      f: Formula,
      t: Expr,
      qvar: Var,
      constructor: (LKProof, SequentIndex, Formula, Expr, Var) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else {
      val List(a_) = pickrule(proof, List(p), List(s._2), List(a))
      val finproof = constructor(s._2, a_, f, t, qvar)
      if (s._1.nonEmpty) {
        val form = s._2.endSequent(s._1.get)
        (Some(finproof.endSequent.indexOfInSuc(form)), finproof)
      } else (None, finproof)
    }
  }

  private def handleSkQuantRule(
      proof: LKProof,
      p: LKProof,
      a: SequentIndex,
      m: Formula,
      t: Expr,
      constructor: (LKProof, SequentIndex, Formula, Expr) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else {
      val List(a_) = pickrule(proof, List(p), List(s._2), List(a))
      val finproof = constructor(s._2, a_, m, t)
      if (s._1.nonEmpty) {
        val form = s._2.endSequent(s._1.get)
        (Some(finproof.endSequent.indexOfInSuc(form)), finproof)
      } else (None, finproof)
    }
  }

  private def handleBinaryRule(
      proof: LKProof,
      p1: LKProof,
      p2: LKProof,
      a1: SequentIndex,
      a2: SequentIndex,
      constructor: (LKProof, SequentIndex, LKProof, SequentIndex) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val new_cut_ancs1 = copySetToAncestor(proof.occConnectors.head, cut_ancs)
    val new_cut_ancs2 = copySetToAncestor(proof.occConnectors(1), cut_ancs)
    val s1 = apply(p1, new_cut_ancs1, pred)
    val s2 = apply(p2, new_cut_ancs2, pred)
    if (cut_ancs(proof.mainIndices.head))
      handleBinaryCutAnc(s1, s2)
    else
      handleBinaryESAnc(proof, p1, p2, s1, s2, constructor)
  }

  private def handleEqRule(
      proof: LKProof,
      p: LKProof,
      e: SequentIndex,
      a: SequentIndex,
      con: Abs,
      constructor: (LKProof, SequentIndex, SequentIndex, Abs) => LKProof,
      pred: Formula => Boolean
  )(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val new_cut_ancs = copySetToAncestor(proof.occConnectors.head, cut_ancs)
    val s1 = apply(p, new_cut_ancs, pred)
    /* distinguish on the cut-ancestorship of the equation (left component) and of the auxiliary formula (right component)
       since the rule does not give direct access to the occurence of e in the conclusion, we look at the premise
     */
    val e_idx_conclusion = proof.occConnectors.head.child(e)
    val aux_ca = cut_ancs(proof.mainIndices.head)
    val eq_ca = cut_ancs(e_idx_conclusion)
    (aux_ca, eq_ca) match {
      case (true, true) =>
        s1
      case (true, false) =>
        s1
      case (false, true) =>
        // we first pick our aux formula
        val candidates = a match {
          case Ant(_) => s1._2.endSequent.zipWithIndex.antecedent
          case Suc(_) => s1._2.endSequent.zipWithIndex.succedent
        }
        val aux = pick(p, a, candidates)
        // then add the weakening
        val wproof = WeakeningLeftRule(s1._2, p.endSequent(e))
        // trace the aux formulas to the new rule
        val conn = wproof.occConnectors(0)
        val waux = conn.child(aux)
        val weq = wproof.mainIndices(0)
        require(waux != weq, "Aux formulas must be different!")
        // and apply it
        val finproof = constructor(wproof, weq, waux, con)
        val form: Option[Formula] =
          if (s1._1.nonEmpty)
            Some(s1._2.endSequent(s1._1.get))
          else None
        if (form.nonEmpty) (Some(finproof.endSequent.indexOfInSuc(form.get)), finproof)
        else (None, finproof)
      case (false, false) =>
        val List(a1_, a2_) = pickrule(proof, List(p), List(s1._2), List(e, a))
        val finproof = constructor(s1._2, a1_, a2_, con)
        val form: Option[Formula] =
          if (s1._1.nonEmpty)
            Some(s1._2.endSequent(s1._1.get))
          else None
        if (form.nonEmpty) (Some(finproof.endSequent.indexOfInSuc(form.get)), finproof)
        else (None, finproof)

    }
  }

  private def handleStrongQuantRule(proof: LKProof, p: LKProof, constructor: (LKProof, SequentIndex, Var, Var) => LKProof, pred: Formula => Boolean)(implicit cut_ancs: Sequent[Boolean]): (Option[SequentIndex], LKProof) = {
    val s = apply(p, copySetToAncestor(proof.occConnectors.head, cut_ancs), pred)
    if (cut_ancs(proof.mainIndices.head)) s
    else throw new Exception("The proof is not skolemized!")
  }
}
