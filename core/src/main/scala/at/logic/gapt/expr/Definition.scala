package at.logic.gapt.expr

case class Definition( what: Const, by: Expr ) {
  val Const( name, ty ) = what
  require( ty == by.ty, s"type $ty of $what and type ${by.ty} of $by must match!" )
  require( freeVariables( by ).isEmpty, s"$this: contains free variables ${freeVariables( by )}" )
  require( typeVariables( by ) subsetOf typeVariables( what ) )

  def toTuple: ( Const, Expr ) = ( what, by )
}