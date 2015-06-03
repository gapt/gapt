/*
 * Simple functions that operate on lambda-expressions
 *
 */

package at.logic.gapt.expr

import at.logic.gapt.expr.{ SymbolA, getRenaming }
import at.logic.gapt.proofs.lk.{ Axiom, BinaryLKProof, UnaryLKProof }
import at.logic.gapt.proofs.lk.base.{ Sequent, FSequent, LKProof }

// Returns a list *without duplicates* of the free variables in the expression.
// There is no guarantee on the ordering of the list.
object freeVariables {
  def apply( e: LambdaExpression ): List[Var] = getFreeVariables( e, List() ).distinct
  def apply( e: FOLExpression ): List[FOLVar] =
    apply( e.asInstanceOf[LambdaExpression] ).asInstanceOf[List[FOLVar]]
  def apply( es: List[FOLExpression] ): List[FOLVar] = es.flatMap( apply( _ ) )

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
    case Var( _, _ )     => List()
    case Const( _, _ )   => List()
    case App( exp, arg ) => boundVariables( exp ) ++ boundVariables( arg )
    case Abs( v, exp )   => v :: boundVariables( exp )
  }
}

/** Returns the set of constants
  *
  */
object constants {
  /**
   *
   * @param e A LambdaExpression
   * @return The set of constant symbols in e
   */
  def apply(e: LambdaExpression): Set[Const] = e match {
    case _: Var => Set()
    case _: LogicalConstant => Set()
    case c: Const => Set(c)
    case App(exp, arg) => constants(exp) union constants(arg)
    case Abs(v, exp) => constants(exp)
  }

  /**
   *
   * @param s An FSequent
   * @return The set of constant symbols in s
   */
  def apply(s: FSequent): Set[Const] = apply(s.toFormula)

  /**
   *
   * @param s A Sequent
   * @return The set of constant symbols in s
   */
  def apply(s: Sequent): Set[Const] = apply(s.toFormula)

  /**
   *
   * @param p An LKProof
   * @return The set of constant symbols in p
   */
  def apply(p: LKProof): Set[Const] = p match {
    case Axiom(seq) => apply(seq)

    case UnaryLKProof(_, u1, seq, _, _) =>
      apply(seq) union apply(u1)

    case BinaryLKProof(_, u1, u2, seq, _, _, _) =>
      apply(seq) union apply(u1) union apply(u2)
  }
}

// get a new variable/constant (similar to the current and) different from all 
// variables/constants in the blackList, returns this variable if this variable 
// is not in the blackList
object rename {
  def apply( v: Var, blackList: List[Var] ): Var = Var( getRenaming( v.sym, blackList.map( v => v.sym ) ), v.exptype )
  def apply( v: FOLVar, blackList: List[Var] ): FOLVar =
    apply( v.asInstanceOf[Var], blackList ).asInstanceOf[FOLVar]
  def apply( a: SymbolA, blackList: List[SymbolA] ): SymbolA = getRenaming( a, blackList )
  def apply( c: Const, blackList: List[Const] ): Const = Const( getRenaming( c.sym, blackList.map( c => c.sym ) ), c.exptype )

  // renames a list of variables to pairwise distinct variables
  // while avoiding names from blackList.
  def apply( vs: Set[FOLVar], blackList: Set[FOLVar] ): Map[FOLVar, FOLVar] = {
    val v_list = vs.toList
    ( v_list zip
      v_list.foldLeft( Nil: List[FOLVar] )(
        ( res, v ) => res :+ apply( v, ( blackList ++ res ).toList ) ) ).toMap
  }
}
