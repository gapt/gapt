package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Eq
import gapt.expr.formula.Imp
import gapt.expr.formula.fol.flatSubterms
import gapt.expr.formula.hol.instantiate
import gapt.provers.escargot.LPO
import gapt.provers.verit.VeriT
import gapt.utils.zipped

object removeSkolemCongruences {

  def repl(m: Map[Expr, Expr], et: ExpansionTree): ExpansionTree =
    ExpansionTree(et.shallow, et.polarity, repl(m, et.term))
  def repl(m: Map[Expr, Expr], et: ETt): ETt = et match {
    case ETtNullary | ETtAtom | ETtWeakening => et
    case ETtMerge(a, b)                      => ETtMerge(repl(m, a), repl(m, b))
    case ETtUnary(a)                         => ETtUnary(repl(m, a))
    case ETtBinary(a, b)                     => ETtBinary(repl(m, a), repl(m, b))
    case ETtStrong(ev, ch)                   => ETtStrong(ev, repl(m, ch))
    case ETtSkolem(Apps(skC, skAs), ch) =>
      val newSkT = skC(TermReplacement(skAs, m))
      ETtSkolem(newSkT, repl(m, ch))
    case ETtWeak(insts) =>
      ETtWeak.withMerge(for ((t, ch) <- insts.view)
        yield TermReplacement(t, m) -> repl(m, ch))
    case ETtDef(_, _) => throw new MatchError(et)
  }

  def remove1(m: Map[Expr, Expr], ep: ExpansionProof): ExpansionProof =
    ExpansionProof(eliminateMerges(ep.expansionSequent.map(et => ETMerge(et, repl(m, et)))))

  def getAllPossibleCongruences(ep: ExpansionProof): Vector[(Expr, Expr)] = {
    val skSyms = ep.skolemSymbols
    val skTerms = flatSubterms(ep.deep.elements).collect {
      case skTerm @ Apps(skSym: Const, _) if skSyms(skSym) => skTerm
    }
    skTerms.groupBy { case Apps(c: Const, _) => c }.values.flatMap(skTs =>
      skTs.subsets(2).map(_.toList).flatMap { s =>
        {
          val List(Apps(_, as), Apps(_, bs)) = s
          as zip bs
        }
      }
    ).toVector
  }

  def getCongruencesViaVeriT(ep: ExpansionProof): Vector[(Expr, Expr)] = {
    val skSyms = ep.skolemSymbols
    val Some(epwc) = VeriT.getExpansionProof(ep.deep): @unchecked
    epwc.expansionSequent.antecedent.flatMap {
      case ETWeakQuantifierBlock(All.Block(_, Imp(_, Eq(Apps(f: Const, _), Apps(f_, _)))), n, insts) if n > 0 && f == f_ && skSyms(f) =>
        insts.flatMap { case (inst, _) => zipped(inst.splitAt(n / 2)).view }
      case _ => Seq()
    }
  }

  def simplCongrs(congrs: Vector[(Expr, Expr)]): Vector[(Expr, Expr)] = {
    val lpo = LPO(containedNames(congrs).collect { case c: Const => c.name }.toSeq.sorted)
    def lt(a: Expr, b: Expr): Boolean = lpo.lt(a, b, true)
    congrs.view.iterator.filter(c => c._1 != c._2).map(c => if (lt(c._1, c._2)) c.swap else c).distinct.toIndexedSeq.sortWith((c1, c2) => lt(c1._1, c2._1)).reverseIterator.toVector
  }

  def remove(ep: ExpansionProof, congrs: Vector[(Expr, Expr)]): ExpansionProof = {
    if (congrs.isEmpty)
      ep
    else {
      val (a, b) +: congrs_ = congrs: @unchecked
      val repl = Map(a -> b)
      val ep_ = remove1(repl, ep)
      remove(
        ep_,
        simplCongrs(congrs_ ++ TermReplacement(congrs_, repl))
      )
    }
  }

  def apply(ep: ExpansionProof): ExpansionProof =
    remove(ep, simplCongrs(getAllPossibleCongruences(ep)))

}
