package at.logic.gapt.expr

import at.logic.gapt.proofs.Context

case class Definition( what: Const, by: Expr ) extends Context.Update {
  val Const( name, ty ) = what
  require( ty == by.ty, s"type $ty of $what and type ${by.ty} of $by must match!" )
  require( freeVariables( by ).isEmpty, s"$this: contains free variables ${freeVariables( by )}" )
  require( typeVariables( by ) subsetOf typeVariables( what ) )

  def toTuple: ( Const, Expr ) = ( what, by )

  override def apply( ctx: Context ): Context.State = {
    ctx.check( what.ty )
    ctx.check( by )
    ctx.state.update[Context.Constants]( _ + what )
      .update[Context.Definitions]( _ + this )
      .update[Context.Reductions]( _ + ( what -> by ) )
  }
}
object Definition {
  implicit def apply( pair: ( Const, Expr ) ): Definition =
    Definition( pair._1, pair._2 )
}