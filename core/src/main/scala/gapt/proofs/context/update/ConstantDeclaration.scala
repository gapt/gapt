package gapt.proofs.context.update

import gapt.expr.Const
import gapt.expr.TVar
import gapt.expr.typeVariables
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.Constants

case class ConstantDeclaration( const: Const ) extends Update {
  override def apply( ctx: Context ): State = {
    ctx.check( const.ty )
    for ( p <- const.params ) require( p.isInstanceOf[TVar] )
    require( typeVariables( const ).toSet subsetOf const.params.toSet )
    ctx.state.update[Constants]( _ + const )
  }
}