package gapt.proofs.context.update

import gapt.expr.Abs
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.FunctionType
import gapt.expr.Quant
import gapt.expr.hol.SkolemFunctions
import gapt.expr.util.freeVariables
import gapt.proofs.context.Context
import gapt.proofs.context.facet.Constants
import gapt.proofs.context.State

case class SkolemFunction( sym: Const, defn: Expr ) extends Update {
  val Abs.Block( argumentVariables, strongQuantifier @ Quant( boundVariable, matrix, isForall ) ) = defn
  require( sym.ty == FunctionType( boundVariable.ty, argumentVariables.map( _.ty ) ) )
  require( freeVariables( defn ).isEmpty )

  override def apply( ctx: Context ): State = {
    ctx.check( sym.ty )
    ctx.check( defn )
    ctx.state.update[Constants]( _ + sym )
      .update[SkolemFunctions]( _ + ( sym, defn ) )
  }
}