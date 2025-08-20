package gapt.logic.hol

import gapt.expr.{Abs, App, Expr, Var}
import gapt.expr.BetaReduction.betaNormalize
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.{All, Eq, Formula, Iff}
import gapt.expr.ty.{FunctionType, To, Ty}
import gapt.expr.util.freeVariables
import gapt.expr.util.rename.awayFrom
import gapt.proofs.{Ant, Sequent, Suc}
import gapt.proofs.expansion.{ExpansionProofToLK, deskolemizeET}
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.*
import gapt.provers.escargot.Escargot

/**
 * Replaces second-order equations between formulas by first-order equivalences.
 */
object soEqToEquiv {

  def apply(p: LKProof): LKProof = {
    p match {
      case peq @ EqualityRule(pi, eq, aux, _) if isSoEq(pi.endSequent(eq)) =>
        val p_ = soEqToEquiv(pi)
        val chi = soEq2Iff(pi.endSequent(aux))
        val chi_ = soEq2Iff(peq.mainFormula)
        val e = soEq2Iff(pi.endSequent(eq))
        val cut = aux match {
          case Ant(_) =>
            val lk = lkProof(e +: chi_ +: Sequent() :+ chi)
            CutRule(lk, p_, chi)
          case Suc(_) =>
            val lk = lkProof(e +: chi +: Sequent() :+ chi_)
            CutRule(p_, lk, chi)
        }
        val Vector(i1, i2) = cut.endSequent.zipWithIndex.antecedent.filter { (f, i) => e == f } map {
          _._2
        } take 2
        ContractionLeftRule(cut, i1, i2)
      case LogicalAxiom(f) => LogicalAxiom(soEq2Iff(f))
      case AndRightRule(l, aux1, r, aux2) =>
        AndRightRule(soEqToEquiv(l), soEq2Iff(l.endSequent(aux1)), soEqToEquiv(r), soEq2Iff(r.endSequent(aux2)))
      case OrLeftRule(l, aux1, r, aux2) =>
        OrLeftRule(soEqToEquiv(l), soEq2Iff(l.endSequent(aux1)), soEqToEquiv(r), soEq2Iff(r.endSequent(aux2)))
      case AndLeftRule(pi, aux1, aux2) =>
        AndLeftRule(soEqToEquiv(pi), soEq2Iff(pi.endSequent(aux1)), soEq2Iff(pi.endSequent(aux2)))
      case OrRightRule(pi, aux1, aux2) =>
        OrRightRule(soEqToEquiv(pi), soEq2Iff(pi.endSequent(aux1)), soEq2Iff(pi.endSequent(aux2)))
      case CutRule(l, aux1, r, aux2) =>
        CutRule(soEqToEquiv(l), soEq2Iff(l.endSequent(aux1)), soEqToEquiv(r), soEq2Iff(r.endSequent(aux2)))
      case ForallLeftRule(pi, aux, f, t, v) =>
        ForallLeftRule(soEqToEquiv(pi), soEq2Iff(p.mainFormulas.head), t)
      case ExistsRightRule(pi, aux, f, t, v) =>
        ExistsRightRule(soEqToEquiv(pi), soEq2Iff(p.mainFormulas.head), t)
      case ForallRightRule(pi, aux, e, v) =>
        ForallRightRule(soEqToEquiv(pi), soEq2Iff(p.mainFormulas.head), e)
      case ExistsLeftRule(pi, aux, e, v) => ExistsLeftRule(soEqToEquiv(pi), soEq2Iff(p.mainFormulas.head), e)
      case WeakeningLeftRule(pi, f)      => WeakeningLeftRule(soEqToEquiv(pi), soEq2Iff(f))
      case WeakeningRightRule(pi, f)     => WeakeningRightRule(soEqToEquiv(pi), soEq2Iff(f))
      case EqualityRightRule(pi, eq, aux, Abs(y, c: Formula)) =>
        EqualityRightRule(apply(pi), soEq2Iff(pi.endSequent(eq)), soEq2Iff(pi.endSequent(aux)), Abs(y, soEq2Iff(c)))
      case EqualityLeftRule(pi, eq, aux, Abs(y, c: Formula)) =>
        EqualityLeftRule(apply(pi), soEq2Iff(pi.endSequent(eq)), soEq2Iff(pi.endSequent(aux)), Abs(y, soEq2Iff(c)))
      case ContractionLeftRule(pi, aux1, aux2) =>
        ContractionLeftRule(apply(pi), soEq2Iff(pi.endSequent(aux1)))
      case ContractionRightRule(pi, aux1, aux2) =>
        ContractionRightRule(apply(pi), soEq2Iff(pi.endSequent(aux1)))
      case ImpLeftRule(l, aux1, r, aux2) => ImpLeftRule(apply(l), soEq2Iff(l.endSequent(aux1)), apply(r), soEq2Iff(r.endSequent(aux2)))
      case ImpRightRule(pi, aux1, aux2)  => ImpRightRule(apply(pi), soEq2Iff(pi.endSequent(aux1)), soEq2Iff(pi.endSequent(aux2)))
      case NegLeftRule(pi, aux)          => NegLeftRule(apply(pi), soEq2Iff(pi.endSequent(aux)))
      case NegRightRule(pi, aux)         => NegRightRule(apply(pi), soEq2Iff(pi.endSequent(aux)))
      case BottomAxiom                   => BottomAxiom
      case TopAxiom                      => TopAxiom
      case ReflexivityAxiom(s) =>
        s.ty match {
          case FunctionType(To, _) => LogicalAxiom(soEq2Iff(Eq(s, s)))
          case _                   => p
        }
    }
  }

  /**
   * A skolem-free LK proof of the provable input sequent.
   */
  private def lkProof(s: Sequent[Formula]): LKProof = {
    val Some(eps) = Escargot.getExpansionProof(s): @unchecked
    val Right(lks) = ExpansionProofToLK(eps): @unchecked
    deskolemizeET(lks)
  }

  private object SoEq {
    def unapply(e: Expr): Option[(Expr, Expr, List[Ty])] = {
      e match {
        case Eq(f1, f2) =>
          (f1.ty, f2.ty) match {
            case (FunctionType(To, ts1), FunctionType(To, ts2)) if ts1 == ts2 =>
              Some(f1, f2, ts1)
            case _ => None
          }
        case _ => None
      }
    }
  }

  private def isSoEq(e: Expr): Boolean = {
    SoEq.unapply(e).isDefined
  }

  def soEq2Iff(f: Formula): Formula = {
    soEq2Iff_(f.asInstanceOf[Expr]).asInstanceOf[Formula]
  }

  private def soEq2Iff_(f: Expr): Expr = {
    f match {
      case SoEq(f1, f2, ts) =>
        val xs = awayFrom(freeVariables(f1) union freeVariables(f2)).freshStream("x").zip(ts).map { (v, t) => Var(v, t) }
        All.Block(xs, Iff(betaNormalize(App(f1, xs)), betaNormalize(App(f2, xs))))
      case App(e1, e2) => App(soEq2Iff_(e1), soEq2Iff_(e2))
      case Abs(x, e)   => Abs(x, soEq2Iff_(e))
      case _           => f
    }
  }
}
