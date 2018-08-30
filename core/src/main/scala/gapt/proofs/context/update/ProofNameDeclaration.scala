package gapt.proofs.context.update

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.TVar
import gapt.expr.Var
import gapt.expr.freeVariables
import gapt.expr.typeVariables
import gapt.proofs.HOLSequent
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.State

case class ProofNameDeclaration( lhs: Expr, endSequent: HOLSequent ) extends Update {
  override def apply( ctx: Context ): State = {
    endSequent.foreach( ctx.check( _ ) )
    val Apps( Const( c, _, ps ), vs ) = lhs
    require( !ctx.get[ProofNames].names.keySet.contains( c ), s"proof already defined: $lhs" )
    require( vs == vs.distinct )
    require( vs.forall( _.isInstanceOf[Var] ) )
    require( ps.forall( _.isInstanceOf[TVar] ) )
    for ( fv <- freeVariables( endSequent ) )
      require( vs.contains( fv ) )
    for ( tv <- typeVariables( endSequent.toImplication ) )
      require( ps.contains( tv ) )
    ctx.state.update[ProofNames]( _ + ( c, lhs, endSequent ) )
  }
}