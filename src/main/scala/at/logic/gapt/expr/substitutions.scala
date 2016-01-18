
package at.logic.gapt.expr

import at.logic.gapt.proofs.HOLSequent

import scala.collection.GenTraversable

/*
 * A substitution is a mapping from variables to lambda-expressions which differs from the identity
 * on finitely many variables. Therefore:
 *  1) each variable is mapped to only one lambda expression
 *  2) the order of the variable-mappings is irrelevant
 *  3) all variable-mappings are applied simultaneously to a term i.e. {x |-> y, y |-> a}x = y and not a.
 *
 * As the lambda calculus contains variable binders, substitution can only be defined up to alpha-equivalence.
 * When applying a substitution, bound variables are renamed if needed.
 */
class Substitution( val map: Map[Var, LambdaExpression] ) {

  // Require that each variable is substituted by a term of the same type
  for ( s <- map ) require(
    s._1.exptype == s._2.exptype,
    "Error creating substitution: variable " + s._1 + " has type " + s._1.exptype +
      " but subterm " + s._2 + " has type " + s._2.exptype
  )

  def apply( t: LambdaExpression ): LambdaExpression = t match {
    case v: Var                           => map.getOrElse( v, v )
    case c: Const                         => c
    case App( a, b )                      => App( apply( a ), apply( b ) )
    case Abs( v, s ) if domain contains v => Substitution( map - v )( t )
    case Abs( v, s ) if range contains v =>
      // It is safe to rename the bound variable to any variable that is not in freeVariables(s).
      val newV = rename( v, freeVariables( s ) union range toList )
      apply( Abs( newV, Substitution( v -> newV )( s ) ) )
    case Abs( v, s ) => Abs( v, apply( s ) )
  }

  def apply( t: HOLFormula ): HOLFormula = apply( t.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]
  def apply( sequent: HOLSequent ): HOLSequent = sequent map apply

  def domain: Set[Var] = map.keySet
  def range: Set[Var] = map.values.toSet[LambdaExpression].flatMap( freeVariables( _ ) )

  def ::( sub: ( Var, LambdaExpression ) ) = new Substitution( map + sub )
  def ::( otherSubstitution: Substitution ) = new Substitution( map ++ otherSubstitution.map )

  override def hashCode = map.hashCode
  override def equals( a: Any ) = a match {
    case s: Substitution => map.equals( s.map )
    case _               => false
  }

  // an identity function maps all variables to themselves
  def isIdentity = map.filterNot( ( p: ( Var, LambdaExpression ) ) => p._1 == p._2 ).isEmpty

  // make sure the overriden keys are of the applying sub
  // note: compose is in function application notation i.e. (sigma compose tau) apply x = sigma(tau(x)) = x.tau.sigma
  def compose( sub: Substitution ): Substitution = Substitution( map ++ sub.map.map( x => ( x._1, apply( x._2 ) ) ) )

  //REMARK: this does not imply the substitution is injective
  def isRenaming = map.forall( p => p._2.isInstanceOf[Var] )

  //TODO: implement
  def isInjectiveRenaming = throw new Exception( "Not yet implemented!" )

  override def toString() = map.map( x => x._1 + " -> " + x._2 ).mkString( "Substitution(", ",", ")" )

}

object Substitution {
  def apply( subs: GenTraversable[( Var, LambdaExpression )] ): Substitution = new Substitution( Map() ++ subs )
  def apply( subs: ( Var, LambdaExpression )* ): Substitution = new Substitution( Map() ++ subs )
  def apply( variable: Var, expression: LambdaExpression ): Substitution = new Substitution( Map( variable -> expression ) )
  def apply( map: Map[Var, LambdaExpression] ): Substitution = new Substitution( map )
  def apply() = new Substitution( Map() )
}

