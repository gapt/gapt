package gapt.proofs.lk.transformations

import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Top
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
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
import gapt.proofs.lk.rules.macros
import gapt.proofs.lk.rules.macros.AndLeftMacroRule
import gapt.proofs.lk.rules.macros.ContractionMacroRule
import gapt.proofs.lk.rules.macros.ImpRightMacroRule
import gapt.proofs.lk.rules.macros.OrRightMacroRule
import gapt.proofs.lk.rules.macros.WeakeningLeftMacroRule

object MG3iToLJ {
  private def mkProjs(fs: List[Formula]): (Formula, Map[Formula, LKProof]) =
    fs match {
      case Nil => (Bottom(), Map.empty)
      case f :: Nil =>
        (f, Map(f -> LogicalAxiom(f)))
      case f :: fs_ =>
        val (d, ps) = mkProjs(fs_)
        (d | f, Map(f -> OrRightMacroRule(LogicalAxiom(f), d, f)) ++ ps.view.mapValues(OrRightMacroRule(_, d, f)).toMap)
    }

  def apply(proof: LKProof): LKProof = proof.conclusion.succedent match {
    case Seq() =>
      val q = CutRule(apply(proof, Bottom(), Map.empty), BottomAxiom, Bottom())
      require(q.conclusion.isSubsetOf(proof.conclusion))
      q
    case Seq(f) =>
      val q = apply(proof, f, Map(f -> LogicalAxiom(f)))
      require(q.conclusion.isSubsetOf(proof.conclusion))
      q
    case fs =>
      val (newSuc, projs) = mkProjs(fs.toList)
      val q = apply(proof, newSuc, projs)
      require(q.conclusion.isSubsetOf(proof.conclusion.copy(succedent = Vector(newSuc))))
      q
  }

  def apply(proof: LKProof, goal: Formula, projections: Map[Formula, LKProof]): LKProof = {
    def withAddGoal(p: LKProof, addGoal: Formula, r: LKProof): LKProof =
      if (!r.conclusion.antecedent.contains(addGoal)) r
      else if (p.conclusion.succedent.forall(_ == addGoal)) {
        val q = apply(p, addGoal, Map(addGoal -> LogicalAxiom(addGoal)))
        val res = ContractionMacroRule(CutRule(q, r, addGoal))
        if (res.conclusion.succedent.isEmpty) WeakeningRightRule(res, goal) else res
      } else {
        val newGoal = goal | addGoal
        val q = apply(
          p,
          newGoal,
          Map() ++
            projections.view.mapValues(pr => CutRule(pr, OrRightMacroRule(LogicalAxiom(goal), goal, addGoal), goal)).toMap +
            (addGoal -> OrRightMacroRule(LogicalAxiom(addGoal), goal, addGoal))
        )
        ContractionMacroRule(CutRule(q, OrLeftRule(LogicalAxiom(goal), r, newGoal), newGoal))
      }
    def rightChain(relativeProjs: (Formula, LKProof)*): Map[Formula, LKProof] =
      projections ++ relativeProjs.map {
        case (f, pr) =>
          val Seq(g) = pr.conclusion.succedent
          f -> ContractionMacroRule(CutRule(pr, projections(g), g))
      }
    macros.ContractionMacroRule(proof match {
      case LogicalAxiom(atom)            => projections(atom)
      case proof @ ReflexivityAxiom(_)   => CutRule(proof, projections(proof.mainFormula), proof.mainFormula)
      case ContractionLeftRule(p, _, _)  => apply(p, goal, projections)
      case ContractionRightRule(p, _, _) => apply(p, goal, projections)
      case WeakeningRightRule(p, _)      => apply(p, goal, projections)
      case WeakeningLeftRule(p, _)       => apply(p, goal, projections)
      case proof @ CutRule(p1, _, p2, _) =>
        val q2 = apply(p2, goal, projections)
        if (!q2.conclusion.antecedent.contains(proof.cutFormula)) q2
        else withAddGoal(p1, proof.cutFormula, q2)
      case BottomAxiom => WeakeningRightRule(BottomAxiom, goal)
      case TopAxiom    => CutRule(TopAxiom, projections(Top()), Top())
      case proof @ EqualityLeftRule(p, _, _, cx) =>
        val q = apply(p, goal, projections)
        if (!q.conclusion.antecedent.contains(proof.auxFormula)) q
        else
          EqualityLeftRule(WeakeningLeftMacroRule(q, proof.equation), proof.equation, proof.auxFormula, cx)
      case proof @ EqualityRightRule(p, _, _, cx) =>
        apply(
          p,
          goal,
          projections + (proof.auxFormula ->
            EqualityLeftRule(WeakeningLeftRule(projections(proof.mainFormula), proof.equation), proof.equation, proof.mainFormula, cx))
        )
      case proof @ AndLeftRule(p, _, _) =>
        val q = apply(p, goal, projections)
        if (q.conclusion.antecedent.contains(proof.leftConjunct) || q.conclusion.antecedent.contains(proof.rightConjunct))
          AndLeftMacroRule(q, proof.leftConjunct, proof.rightConjunct)
        else q
      case proof @ OrLeftRule(p1, _, p2, _) =>
        val q1 = apply(p1, goal, projections)
        if (!q1.conclusion.antecedent.contains(proof.leftDisjunct)) q1
        else {
          val q2 = apply(p2, goal, projections)
          if (!q2.conclusion.antecedent.contains(proof.rightDisjunct)) q2
          else
            OrLeftRule(q1, proof.leftDisjunct, q2, proof.rightDisjunct)
        }
      case proof @ ImpLeftRule(p1, _, p2, _) =>
        val q2 = apply(p2, goal, projections)
        if (!q2.conclusion.antecedent.contains(proof.impConclusion)) q2
        else withAddGoal(p1, proof.impPremise, ImpLeftRule(LogicalAxiom(proof.impPremise), proof.impPremise, q2, proof.impConclusion))
      case proof @ NegLeftRule(p, _) =>
        withAddGoal(p, proof.auxFormula, NegLeftRule(LogicalAxiom(proof.auxFormula), proof.auxFormula))
      case proof @ AndRightRule(p1, _, p2, _) =>
        val q2 = apply(
          p2,
          goal,
          rightChain(proof.rightConjunct ->
            AndRightRule(LogicalAxiom(proof.leftConjunct), LogicalAxiom(proof.rightConjunct), proof.mainFormula))
        )
        withAddGoal(p1, proof.leftConjunct, q2)
      case proof @ OrRightRule(p1, _, _) =>
        apply(
          p1,
          goal,
          rightChain(
            proof.leftDisjunct ->
              OrRightMacroRule(LogicalAxiom(proof.leftDisjunct), proof.leftDisjunct, proof.rightDisjunct),
            proof.rightDisjunct ->
              OrRightMacroRule(LogicalAxiom(proof.rightDisjunct), proof.leftDisjunct, proof.rightDisjunct)
          )
        )
      case proof @ ExistsRightRule(p, _, _, _, _) =>
        apply(
          p,
          goal,
          rightChain(proof.auxFormula ->
            ExistsRightRule(LogicalAxiom(proof.auxFormula), proof.mainFormula, proof.term))
        )
      case proof @ ExistsLeftRule(p, _, _, _) =>
        val q = apply(p, goal, projections)
        if (!q.conclusion.antecedent.contains(proof.auxFormula)) q
        else
          ExistsLeftRule(q, proof.mainFormula, proof.eigenVariable)
      case proof @ ForallLeftRule(p, _, _, _, _) =>
        val q = apply(p, goal, projections)
        if (!q.conclusion.antecedent.contains(proof.auxFormula)) q
        else
          ForallLeftRule(q, proof.mainFormula, proof.term)
      case proof @ NegRightRule(p, _) =>
        require(p.conclusion.succedent.isEmpty)
        val q = CutRule(apply(p, Bottom(), Map()), BottomAxiom, Bottom())
        CutRule(
          if (!q.conclusion.antecedent.contains(proof.auxFormula)) q else NegRightRule(q, proof.auxFormula),
          projections(proof.mainFormula),
          proof.mainFormula
        )
      case proof @ ImpRightRule(p, _, _) =>
        require(p.conclusion.succedent.size == 1)
        val q = apply(p, proof.impConclusion, Map(proof.impConclusion -> LogicalAxiom(proof.impConclusion)))
        CutRule(ImpRightMacroRule(q, proof.impPremise, proof.impConclusion), projections(proof.mainFormula), proof.mainFormula)
      case proof @ ForallRightRule(p, _, _, _) =>
        require(p.conclusion.succedent.size == 1)
        val q = apply(p, proof.auxFormula, Map(proof.auxFormula -> LogicalAxiom(proof.auxFormula)))
        CutRule(ForallRightRule(q, proof.mainFormula, proof.eigenVariable), projections(proof.mainFormula), proof.mainFormula)
    })
  }
}
