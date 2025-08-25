package gapt.proofs.context.mutable

import gapt.expr.Abs
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Replaceable
import gapt.expr.containedNames
import gapt.expr.formula.Quant
import gapt.expr.ty.FunctionType
import gapt.expr.ty.baseTypes
import gapt.expr.util.constants
import gapt.expr.util.typeVariables
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.Definitions
import gapt.proofs.context.facet.skolemFunsFacet
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.update.Definition
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.Update
import gapt.proofs.context.update.{SkolemFunction => SkolemFun}
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.lkProofReplaceable
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.resolution.resolutionProofsAreReplaceable

class MutableContext(
    private var ctx_ : ImmutableContext
) extends Context
    with ReadOnlyMutableContext
    with WriteOnlyMutableContext {

  override def state: State = ctx.state
  override def updates: List[Update] = ctx.updates
  override def toImmutable: ImmutableContext = ctx

  override def toString: String = ctx.toString

  def ctx: ImmutableContext = ctx_
  def ctx_=(newCtx: ImmutableContext): Unit = ctx_ = newCtx

  def +=(update: Update): Unit = ctx += update
  def ++=(updates: Iterable[Update]): Unit = ctx ++= updates

  def addDefinition(by: Expr, name: => String = newNameGenerator.freshWithIndex("D"), reuse: Boolean = true): Const = scala.util.boundary {
    if (reuse) {
      for ((d, _) <- get[Definitions].definitions.find(_._2 == by)) {
        scala.util.boundary.break(Const(d, by.ty))
      }
    }
    val what = Const(name, by.ty, typeVariables(by).toList)
    this += Definition(what, by)
    what
  }

  def addSkolemSym(defn: Expr, name: => String = newNameGenerator.freshWithIndex("s"), reuse: Boolean = true): Const = scala.util.boundary {
    if (reuse) {
      for ((d, _) <- get[SkolemFunctions].skolemDefs.find(_._2 == defn)) {
        scala.util.boundary.break(d)
      }
    }
    val Abs.Block(vs, Quant(v, _, _)) = defn: @unchecked
    val sym = Const(name, FunctionType(v.ty, vs.map(_.ty)))
    this += SkolemFun(sym, defn)
    sym
  }
}
object MutableContext {
  def default(): MutableContext = Context.default.newMutable
  def guess(exprs: Iterable[Expr]): MutableContext = Context.guess(exprs).newMutable
  def guess(exprs: Expr*): MutableContext = guess(exprs)
  def guess(seq: Sequent[Expr]): MutableContext = guess(seq.elements)
  def guess(cnf: Iterable[Sequent[Expr]])(implicit dummyImplicit: DummyImplicit): MutableContext = guess(cnf.view.flatMap(_.elements))
  def guess[R, S](rs: Iterable[R])(implicit ev: Replaceable[R, S]): MutableContext =
    guess(rs.view.flatMap(ev.names))
  def guess(p: LKProof): MutableContext =
    guess(containedNames(p)) // TODO: add (Skolem) definitions

  def guess(p: ResolutionProof): MutableContext = {
    val ctx = default()

    val cs = containedNames(p)

    val tys = cs.flatMap(c => baseTypes(c.ty))
    for (ty <- tys if !ctx.isType(ty))
      ctx += Sort(ty)

    val defs: Map[Const, Expr] = p.definitions.toMap
    def add(c: Const): Unit =
      if (ctx.constant(c.name).isEmpty) defs.get(c) match {
        case Some(d) =>
          constants.nonLogical(d).foreach(add)
          ctx += Definition(c, d)
        case None =>
          ctx += c
      }
    cs.foreach {
      case c: Const => add(c)
      case _        =>
    }

    ctx
  }
}
