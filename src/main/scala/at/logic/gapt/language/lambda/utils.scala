/*
 * Simple functions that operate on lambda-expressions
 *
 */

package at.logic.gapt.language.lambda

import at.logic.gapt.language.lambda.symbols.{ SymbolA, getRenaming }

// Returns a list *without duplicates* of the free variables in the expression.
// There is no guarantee on the ordering of the list.
object freeVariables {
  def apply( e: LambdaExpression ): List[Var] = getFreeVariables( e, List() ).distinct

  private def getFreeVariables( e: LambdaExpression, bound: List[Var] ): List[Var] = e match {
    case v: Var =>
      if ( !bound.contains( v ) ) List( v )
      else List()
    case Const( _, _ )   => List()
    case App( exp, arg ) => getFreeVariables( exp, bound ) ++ getFreeVariables( arg, bound )
    case Abs( v, exp )   => getFreeVariables( exp, v :: bound )
  }
}

// Returns a list *with duplicates* of the bound variables in the expression.
// There is no guarantee on the ordering of the list.
object boundVariables {
  def apply( e: LambdaExpression ): List[Var] = e match {
    case Var( _, _ ) => List()
    case Const( _, _ )   => List()
    case App( exp, arg ) => boundVariables( exp ) ++ boundVariables( arg )
    case Abs( v, exp )   => v :: boundVariables( exp )
  }
}

// get a new variable/constant (similar to the current and) different from all 
// variables/constants in the blackList, returns this variable if this variable 
// is not in the blackList
object rename {
  def apply( v: Var, blackList: List[Var] ): Var = v.factory.createVar( getRenaming( v.sym, blackList.map( v => v.sym ) ), v.exptype )
  def apply( a: SymbolA, blackList: List[SymbolA] ): SymbolA = getRenaming( a, blackList )
  def apply( c: Const, blackList: List[Const] ): Const = c.factory.createConst( getRenaming( c.sym, blackList.map( c => c.sym ) ), c.exptype )
}

