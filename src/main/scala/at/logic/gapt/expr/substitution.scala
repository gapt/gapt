package at.logic.gapt.expr

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

  /**
   * Applies this substitution to an object.
   *
   * @param x The object to be substituted.
   * @param ev Testifies that applying a Substitution to an element of type T will result in an element of type U.
   * @tparam T The type of x.
   * @tparam U The type of x substituted.
   * @return
   */
  def apply[T, U]( x: T )( implicit ev: Substitutable[Substitution, T, U] ): U = ev.applySubstitution( this, x )

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
  def compose( sub: Substitution ): Substitution = {
    val newMap = for ( ( x1, x2 ) <- sub.map ) yield {
      val x2_ = apply( x2 )
      ( x1, x2_ )
    }
    Substitution( map ++ newMap )
  }

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

class FOLSubstitution( val folmap: Map[FOLVar, FOLTerm] ) extends Substitution( folmap.asInstanceOf[Map[Var, LambdaExpression]] ) {
  /**
   * Applies this substitution to an object.
   *
   * @param x The object to be substituted.
   * @param ev Testifies that applying a FOLSubstitution to an element of type T will result in an element of type U.
   * @tparam T The type of x.
   * @tparam U The type of x substituted.
   * @return
   */
  def apply[T, U]( x: T )( implicit ev: Substitutable[FOLSubstitution, T, U], dummyImplicit: DummyImplicit ): U = ev.applySubstitution( this, x )

  def compose( sub: FOLSubstitution ): FOLSubstitution = {
    val newMap = for ( ( x1, x2 ) <- sub.folmap ) yield {
      val x2_ = apply( x2 )
      ( x1, x2_ )
    }
    FOLSubstitution( folmap ++ newMap )
  }
}
object FOLSubstitution {
  def apply( subs: GenTraversable[( FOLVar, FOLTerm )] ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( subs: ( FOLVar, FOLTerm )* ): FOLSubstitution = new FOLSubstitution( Map() ++ subs )
  def apply( variable: FOLVar, term: FOLTerm ): FOLSubstitution = new FOLSubstitution( Map( variable -> term ) )
  def apply( map: Map[FOLVar, FOLTerm] ): FOLSubstitution = new FOLSubstitution( map )
  def apply() = new FOLSubstitution( Map() )
}
