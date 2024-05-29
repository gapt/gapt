package gapt.proofs.resolution

import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.proofs.{Ant, Suc, SequentFlattenOp}
import gapt.proofs.lk._
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.macros.ContractionMacroRule

object UnitResolutionToLKProof {

  def apply(proof: ResolutionProof): LKProof = {

    def shouldFlip(p: ResolutionProof): Boolean = p match {
      case Paramod(_, _, _, q, _, _) => shouldFlip(q)
      case Flip(q, _)                => !shouldFlip(q)
      case Input(_)                  => false
    }
    def maybeFlip(atom: Formula, flip: Boolean): Formula =
      if (flip) {
        val Eq(t, s) = atom: @unchecked
        Eq(s, t)
      } else {
        atom
      }

    var lk: LKProof = proof match {
      case Resolution(Refl(term), _, _, _) => ReflexivityAxiom(term)
      case Resolution(left, _, right, _) =>
        val sucEq = maybeFlip(right.conclusion(Ant(0)), shouldFlip(right))
        val antEq = maybeFlip(left.conclusion(Suc(0)), shouldFlip(left))
        (antEq, sucEq) match {
          case (x, y) if x == y => LogicalAxiom(x)
          case (Eq(t, s), Eq(s_, t_)) if t == t_ && s == s_ =>
            ResolutionToLKProof.mkSymmProof(t, s)
        }
    }

    proof.dagLike.postOrder.reverse.tail.foreach { p =>
      p match {
        case Refl(_)  =>
        case Input(_) =>
        case p @ Paramod(q1, _, _, q2, i2, ctx) =>
          val shouldFlip2 = shouldFlip(q2)
          val lkAux = maybeFlip(p.rewrittenAuxFormula, shouldFlip2)
          if (lk.conclusion.contains(lkAux, !i2.polarity)) {
            val lkMain = maybeFlip(p.auxFormula, shouldFlip2)
            val lkEq = maybeFlip(q1.conclusion(Suc(0)), shouldFlip(q1))
            if ((i2.isSuc && lkEq == lkAux) || !lk.conclusion.antecedent.contains(lkEq)) {
              lk = WeakeningLeftRule(lk, lkEq)
            }
            if (i2.isSuc)
              lk = EqualityLeftRule(lk, lkEq, lkAux, lkMain)
            else
              lk = EqualityRightRule(lk, lkEq, lkAux, lkMain)
          }
        case Flip(_, _) =>
      }

      if (lk.conclusion.isTaut) {
        lk = LogicalAxiom(lk.conclusion.antecedent intersect lk.conclusion.succedent head)
      } else {
        lk = ContractionMacroRule(lk)
      }
    }

    val expectedConclusion = proof.subProofs.collect { case Input(seq) => seq.swapped }.flattenS

    require(
      lk.conclusion isSubMultisetOf expectedConclusion,
      s"$expectedConclusion\n$proof\n$lk"
    )

    lk
  }

}
