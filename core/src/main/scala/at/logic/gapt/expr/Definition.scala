package at.logic.gapt.expr

case class Definition( what: Const, by: LambdaExpression ) {
  val Const( name, ty ) = what
  require( ty == by.exptype, s"type $ty of $what and type ${by.exptype} of $by must match!" )
  require( freeVariables( by ).isEmpty, s"$this: contains free variables ${freeVariables( by )}" )
  require( typeVariables( by ) subsetOf typeVariables( what ) )

  def toTuple: ( Const, LambdaExpression ) = ( what, by )
}