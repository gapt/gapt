package at.logic.gapt.expr

case class Definition( what: Const, by: LambdaExpression ) {
  val Const( name, ty ) = what
  require( ty == by.exptype )
  require( freeVariables( by ).isEmpty, s"$this: contains free variables ${freeVariables( by )}" )

  def toTuple: ( Const, LambdaExpression ) = ( what, by )
}