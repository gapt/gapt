package gapt.proofs

import gapt.expr._
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.expr.util.freeVariables
import gapt.expr.util.typeVariables
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.Definition
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.{ConstantDeclaration => ConstDecl}
import gapt.proofs.context.update.{SkolemFunction => SkolemFun}
import gapt.proofs.context.update.Update

import scala.collection.mutable

class ContextSection(ctx: MutableContext) {
  private val initialCtx: ImmutableContext = ctx.ctx
  private val parameters = mutable.Map[Const, Var]()
  private val tyParameters = mutable.Map[TBase, TVar]()

  def addParameter(c: TBase, v: TVar): Unit = {
    ctx += c
    tyParameters(c) = v
  }

  def addParameter(c: Const, v: Var): Unit = {
    ctx += c
    parameters(c) = v
  }

  def groundSequent(seq: HOLSequent): HOLSequent = {
    val nameGen = ctx.newNameGenerator
    val tyGrounding = Substitution(
      Map(),
      Map() ++
        (for (t <- typeVariables(seq.elements)) yield {
          val c = TBase(nameGen.fresh(t.name))
          addParameter(c, t)
          t -> c
        })
    )
    val grounding = Substitution(
      for (v @ Var(n, t) <- freeVariables(seq)) yield {
        val c = Const(nameGen.fresh(n), tyGrounding(t))
        addParameter(c, v)
        v -> c
      },
      tyGrounding.typeMap
    )
    grounding(seq)
  }

  def revert[T: ClosedUnderReplacement](t: T): T = {
    val updatesSinceSectionBegin = ctx.updates.dropRight(initialCtx.updates.size)
    ctx.ctx = initialCtx
    val repl = revertParameters(updatesSinceSectionBegin, parameters.toMap, tyParameters.toMap)(ctx)
    TermReplacement(t, repl._1, repl._2)
  }
}

object withSection {
  def apply[T: ClosedUnderReplacement](f: ContextSection => T)(implicit ctx: MutableContext): T = {
    val section = new ContextSection(ctx)
    val t = f(section)
    section.revert(t)
  }
}

private object revertParameters {
  def apply(
      update: Update,
      replacements: Map[Const, Expr],
      tyReplacements: Map[TBase, Ty]
  )(implicit ctx: MutableContext): (Map[Const, Expr], Map[TBase, Ty]) =
    update match {
      case ConstDecl(c) if replacements contains c =>
        replacements -> tyReplacements

      case Sort(t) if tyReplacements contains t =>
        replacements -> tyReplacements

      case Definition(what0, by0) =>
        val what = TermReplacement(what0: Expr, replacements, tyReplacements).asInstanceOf[Const]
        val by = TermReplacement(by0, replacements, tyReplacements)
        val fvs = freeVariables(by).toList
        val tvs = typeVariables(by).toList
        if (fvs.isEmpty && tvs.isEmpty) {
          ctx += Definition(what, by)
          replacements -> tyReplacements
        } else {
          val by1 = Abs(fvs, by)
          val what1 = Const(what.name, FunctionType(what.ty, fvs.map(_.ty)), tvs)
          ctx += Definition(what1, by1)
          replacements + (what0 -> Apps(what1, fvs)) -> tyReplacements
        }

      case SkolemFun(sym0, defn0) =>
        val defn = TermReplacement(defn0, replacements, tyReplacements)
        val sym = TermReplacement(sym0: Expr, replacements, tyReplacements).asInstanceOf[Const]
        val fvs = freeVariables(defn).toList
        val tvs = typeVariables(defn).toList
        if (fvs.isEmpty && tvs.isEmpty) {
          ctx += SkolemFun(sym, defn)
          replacements -> tyReplacements
        } else {
          val defn1 = Abs(fvs, defn)
          val sym1 = Const(sym.name, FunctionType(sym.ty, fvs.map(_.ty)), tvs)
          ctx += SkolemFun(sym1, defn1)
          replacements + (sym0 -> Apps(sym1, fvs)) -> tyReplacements
        }

      case _ =>
        ctx += update
        replacements -> tyReplacements
    }

  def apply(updates: List[Update], replacements: Map[Const, Expr], tyReplacements: Map[TBase, Ty])(implicit ctx: MutableContext): (Map[Const, Expr], Map[TBase, Ty]) =
    updates.foldRight(replacements -> tyReplacements)((up, repl) => revertParameters(up, repl._1, repl._2))
}
