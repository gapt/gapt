package gapt.proofs.lk.transformations

import gapt.expr.Abs
import gapt.expr.formula._
import gapt.expr.formula.hol.instantiate
import gapt.expr.util.freeVariables
import gapt.proofs.lk.rules._
import gapt.proofs.lk.rules.macros.ContractionMacroRule
import gapt.proofs.lk.{LKProof, LKVisitor}
import gapt.proofs.{SequentConnector, SequentIndex}

object pushEqualityInferencesToLeaves2 extends LKVisitor[Unit] {

  /**
   * Pushes a single equality inferences as far to the leaves as possible,
   * that is, until it reaches an initial sequent or another equality inference.
   */
  def push(p: LKProof, eq: Formula, aux: SequentIndex, ctx: Abs): LKProof = {
    lazy val mkEquality: EqualityRule = {
      val q = WeakeningLeftRule(p, eq)
      EqualityRule(q, q.mainIndices.head, q.getSequentConnector.child(aux), ctx)
    }

    def pushUnary(p: UnaryLKProof, ctx: Abs = ctx): LKProof =
      push(p.subProof, eq, p.getSequentConnector.parent(aux), ctx)
    def pushI(p: LKProof, i: Int, ctx: Abs): LKProof =
      p.occConnectors(i).parentOption(aux) match {
        case Some(aux_) => push(p.immediateSubProofs(i), eq, aux_, ctx)
        case None       => p.immediateSubProofs(i)
      }
    def pushLeft(p: BinaryLKProof, ctx: Abs = ctx): LKProof = pushI(p, 0, ctx)
    def pushRight(p: BinaryLKProof, ctx: Abs = ctx): LKProof = pushI(p, 1, ctx)

    // unary inferences with two aux fmls
    def pushUnary2(p: UnaryLKProof, ctx1: Abs, ctx2: Abs): LKProof = {
      val Seq(Seq(aux1, aux2)) = p.auxIndices
      (freeVariables(ctx1.term)(ctx1.variable), freeVariables(ctx2.term)(ctx2.variable)) match {
        case (false, false) => p.subProof
        case (true, false)  => push(p.subProof, eq, aux1, ctx1)
        case (false, true)  => push(p.subProof, eq, aux2, ctx2)
        case (true, true) =>
          val q = push(p.subProof, eq, aux1, ctx1)
          push(q, eq, q.endSequent.indexOf(p.subProof.endSequent(aux2), aux2.polarity), ctx2)
      }
    }

    p match {
      case InitialSequent(_) | EqualityRule(_, _, _, _) => mkEquality

      case p: WeakeningLeftRule if aux != p.mainIndices.head =>
        WeakeningLeftRule(pushUnary(p), p.mainFormula)
      case p: WeakeningRightRule if aux != p.mainIndices.head =>
        WeakeningRightRule(pushUnary(p), p.mainFormula)
      case p: ContractionLeftRule if aux != p.mainIndices.head =>
        ContractionLeftRule(pushUnary(p), p.mainFormula)
      case p: ContractionRightRule if aux != p.mainIndices.head =>
        ContractionRightRule(pushUnary(p), p.mainFormula)

      case p @ WeakeningLeftRule(q, _) if aux == p.mainIndices.head =>
        WeakeningLeftRule(q, mkEquality.mainFormula)
      case p @ WeakeningRightRule(q, _) if aux == p.mainIndices.head =>
        WeakeningRightRule(q, mkEquality.mainFormula)

      case p: ContractionRule if aux == p.mainIndices.head =>
        val q = push(p.subProof, eq, p.getSequentConnector.parents(aux).head, ctx)
        val r = push(q, eq, q.endSequent.indexOf(p.endSequent(aux), aux.polarity), ctx)
        if (aux.isAnt)
          ContractionLeftRule(r, mkEquality.mainFormula)
        else
          ContractionRightRule(r, mkEquality.mainFormula)

      case p: NegLeftRule if aux != p.mainIndices.head =>
        NegLeftRule(pushUnary(p), p.auxFormula)
      case p: NegRightRule if aux != p.mainIndices.head =>
        NegRightRule(pushUnary(p), p.auxFormula)
      case p: AndLeftRule if aux != p.mainIndices.head =>
        AndLeftRule(pushUnary(p), p.mainFormula)
      case p: OrRightRule if aux != p.mainIndices.head =>
        OrRightRule(pushUnary(p), p.mainFormula)
      case p: ImpRightRule if aux != p.mainIndices.head =>
        ImpRightRule(pushUnary(p), p.mainFormula)
      case p @ StrongQuantifierRule(q, i, ev, qv, isForall) if aux != p.mainIndices.head =>
        StrongQuantifierRule(pushUnary(p), p.mainFormula, ev, isForall)
      case p @ WeakQuantifierRule(q, i, f, t, v, isExists) if aux != p.mainIndices.head =>
        WeakQuantifierRule(pushUnary(p), p.mainFormula, t, isExists)

      case p: AndRightRule if aux != p.mainIndices.head =>
        AndRightRule(pushLeft(p), pushRight(p), p.mainFormula)
      case p: OrLeftRule if aux != p.mainIndices.head =>
        OrLeftRule(pushLeft(p), pushRight(p), p.mainFormula)
      case p: ImpLeftRule if aux != p.mainIndices.head =>
        ImpLeftRule(pushLeft(p), pushRight(p), p.mainFormula)

      case p: CutRule =>
        CutRule(pushLeft(p), pushRight(p), p.cutFormula)

      case p @ StrongQuantifierRule(_, _, ev, _, isForall) if aux == p.mainIndices.head =>
        val Abs(x, f: Formula) = ctx: @unchecked
        require(x != ev)
        StrongQuantifierRule(pushUnary(p, Abs(x, instantiate(f, ev))), mkEquality.mainFormula, ev, isForall)
      case p @ WeakQuantifierRule(_, _, _, t, _, isExists) if aux == p.mainIndices.head =>
        val Abs(x, f: Formula) = ctx: @unchecked
        require(!freeVariables(t)(x))
        WeakQuantifierRule(pushUnary(p, Abs(x, instantiate(f, t))), mkEquality.mainFormula, t, isExists)

      case p: SkolemQuantifierRule if aux == p.mainIndices.head =>
        val Abs(x, f: Formula) = ctx: @unchecked
        require(!freeVariables(p.skolemTerm)(x))
        val q = pushUnary(p, Abs(x, instantiate(f, p.skolemTerm)))
        if (aux.isAnt)
          ExistsSkLeftRule(q, mkEquality.mainFormula, p.skolemTerm)
        else
          ForallSkRightRule(q, mkEquality.mainFormula, p.skolemTerm)

      case p: NegLeftRule if aux == p.mainIndices.head =>
        val Abs(x, Neg(f)) = ctx: @unchecked
        val Neg(newAux) = mkEquality.mainFormula: @unchecked
        NegLeftRule(pushUnary(p, Abs(x, f)), newAux)
      case p: NegRightRule if aux == p.mainIndices.head =>
        val Abs(x, Neg(f)) = ctx: @unchecked
        val Neg(newAux) = mkEquality.mainFormula: @unchecked
        NegRightRule(pushUnary(p, Abs(x, f)), newAux)

      case p: AndLeftRule if aux == p.mainIndices.head =>
        val Abs(x, And(f, g)) = ctx: @unchecked
        AndLeftRule(pushUnary2(p, Abs(x, f), Abs(x, g)), mkEquality.mainFormula)
      case p: OrRightRule if aux == p.mainIndices.head =>
        val Abs(x, Or(f, g)) = ctx: @unchecked
        OrRightRule(pushUnary2(p, Abs(x, f), Abs(x, g)), mkEquality.mainFormula)
      case p: ImpRightRule if aux == p.mainIndices.head =>
        val Abs(x, Imp(f, g)) = ctx: @unchecked
        ImpRightRule(pushUnary2(p, Abs(x, f), Abs(x, g)), mkEquality.mainFormula)
    }
  }

  def push(proof: EqualityRule): LKProof =
    ContractionMacroRule(push(proof.subProof, proof.equation, proof.aux, proof.replacementContext))

  def visitEquality(proof: EqualityRule): (LKProof, SequentConnector) =
    push(proof) match { case q => q -> SequentConnector.guessInjection(q.endSequent, proof.endSequent) }

  override def visitEqualityLeft(proof: EqualityLeftRule, otherArg: Unit): (LKProof, SequentConnector) =
    visitEquality(proof)

  override def visitEqualityRight(proof: EqualityRightRule, otherArg: Unit): (LKProof, SequentConnector) =
    visitEquality(proof)

  def apply(p: LKProof): LKProof = super.apply(p, ())

}
