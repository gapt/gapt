package gapt.expr

import gapt.expr.util.freeVariables
import gapt.expr.util.typeVariables
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.Constants
import gapt.proofs.context.facet.Definitions
import gapt.proofs.context.facet.Reductions
import gapt.proofs.context.update.Update

case class Definition( what: Const, by: Expr ) extends Update {
  val Const( name, ty, ps ) = what
  require( ps.forall( _.isInstanceOf[TVar] ), s"type parameters $ps must be variables" )
  require( ty == by.ty, s"type $ty of $what and type ${by.ty} of $by must match!" )
  require( freeVariables( by ).isEmpty, s"$this: contains free variables ${freeVariables( by )}" )
  require( typeVariables( by ).toSet subsetOf ps.toSet )
  require( typeVariables( what ).toSet subsetOf ps.toSet )

  def toTuple: ( Const, Expr ) = ( what, by )

  override def apply( ctx: Context ): State = {
    ctx.check( what.ty )
    ctx.check( by )
    ctx.state.update[Constants]( _ + what )
      .update[Definitions]( _ + this )
      .update[Reductions]( _ + ( what -> by ) )
  }
}
object Definition {
  implicit def apply( pair: ( Const, Expr ) ): Definition =
    Definition( pair._1, pair._2 )
}