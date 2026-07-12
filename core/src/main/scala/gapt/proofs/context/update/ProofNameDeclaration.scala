package gapt.proofs.context.update

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.ty.TVar
import gapt.expr.util.freeVariables
import gapt.expr.util.typeVariables
import gapt.proofs.HOLSequent
import gapt.proofs.RichFormulaSequent
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.State

case class ProofNameDeclaration(lhs: Expr, endSequent: HOLSequent, captured_variables : Set[Var] = Set()) extends Update {
  override def apply(ctx: Context): State = {
    endSequent.foreach(ctx.check(_))
    val Apps(Const(c, _, ps), vs) = lhs: @unchecked
    require(!ctx.get[ProofNames].names.keySet.contains(c), s"proof already defined: $lhs")
    require(vs == vs.distinct, s"definition variables $vs must be distinct")
    require(vs.forall(_.isInstanceOf[Var]),s"definition variables $vs must be variables")
    require(ps.forall(_.isInstanceOf[TVar]), s"parametric types $ps of definition must be type variables")
    for (fv <- freeVariables(endSequent) diff captured_variables)
      require(vs.contains(fv), s"free variable $fv in end-sequent is not a free variable in definition $lhs (ignoring ${captured_variables.mkString("{", ", ", "}")})")
    for (tv <- typeVariables(endSequent.toImplication))
      require(ps.contains(tv), s"free type variable $tv is not a free type variable of definition ($ps)")
    ctx.state.update[ProofNames](_.+(c, lhs, endSequent))
  }
}
