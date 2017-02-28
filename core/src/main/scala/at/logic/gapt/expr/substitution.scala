package at.logic.gapt.expr

import at.logic.gapt.expr.Substitutable.SubstitutableTy

import scala.collection.GenTraversable

/**
 * An unvalidated substitution, you should use [[Substitution]] instead.
 */
class PreSubstitution( val map: Map[Var, LambdaExpression], val typeMap: Map[TVar, Ty] ) {

  def domain: Set[Var] = map.keySet
  def range: Set[Var] = map.values.toSet[LambdaExpression].flatMap( freeVariables( _ ) )

  override def hashCode: Int = map.hashCode ^ typeMap.hashCode

  override def equals( a: Any ): Boolean = a match {
    case s: PreSubstitution => map == s.map && typeMap == s.typeMap
    case _                  => false
  }

  def isIdentity: Boolean = map.forall( p => p._1 == p._2 ) && typeMap.forall( p => p._1 == p._2 )

  def isRenaming: Boolean = map.forall( p => p._2.isInstanceOf[Var] )

  def isInjectiveRenaming: Boolean = domain.forall { v => map( v ).isInstanceOf[Var] && domain.forall { u => u == v || map( u ) != map( v ) } }

  def isEmpty: Boolean = map.isEmpty && typeMap.isEmpty

  override def toString: String =
    s"Substitution(${
      ( map.toSeq.sortBy( _._1.name ) ++ typeMap.toSeq.sortBy( _._1.name ) ).
        map( x => s"${x._1} -> ${x._2}" ).mkString( ", " )
    })"

  def asFOLSubstitution: FOLSubstitution = {
    require( typeMap.isEmpty )
    FOLSubstitution( map map { case ( l: FOLVar, r: FOLTerm ) => l -> r } )
  }

  def +( v: Var, t: LambdaExpression ): PreSubstitution = new PreSubstitution( map + ( ( v, t ) ), typeMap )
  def +( v: TVar, t: Ty ): PreSubstitution = new PreSubstitution( map, typeMap + ( ( v, t ) ) )

  def toSubstitution: Substitution = Substitution( map, typeMap )

}

object PreSubstitution {
  def apply(): PreSubstitution = new PreSubstitution( Map(), Map() )
  def apply( map: Traversable[( Var, LambdaExpression )] ): PreSubstitution = new PreSubstitution( map.toMap, Map() )
}

/**
 * A substitution is a mapping from variables to lambda-expressions which differs from the identity
 * on finitely many variables. Therefore:
 *  1) each variable is mapped to only one lambda expression
 *  2) the order of the variable-mappings is irrelevant
 *  3) all variable-mappings are applied simultaneously to a term i.e. {x |-> y, y |-> a}x = y and not a.
 *
 * As the lambda calculus contains variable binders, substitution can only be defined up to alpha-equivalence.
 * When applying a substitution, bound variables are renamed if needed.
 */
class Substitution( map: Map[Var, LambdaExpression], typeMap: Map[TVar, Ty] = Map() ) extends PreSubstitution( map, typeMap ) {

  for ( ( v, t ) <- map )
    require(
      SubstitutableTy.applySubstitution( this, v.exptype ) == t.exptype,
      s"Error creating substitution: variable $v has type ${v.exptype} but subterm $t has type ${t.exptype}"
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

  /** Compose two substitutions such that `(a compose b)(x) == a(b(x))`. */
  def compose( that: Substitution ): Substitution =
    Substitution(
      ( domain ++ that.domain ).map( v => v -> this( that( v ) ) ),
      ( this.typeMap.keySet ++ that.typeMap.keySet ).map( v => ( v, this( that( v ) ) ) )
    )

  def restrict( newDomain: Iterable[Var] ): Substitution =
    Substitution( newDomain.view.map( v => v -> this( v ) ) )

  def isInjectiveOnDomain: Boolean = isInjective( domain )
  def isInjective( dom: Set[Var] ): Boolean =
    dom.forall { x =>
      val images = ( dom - x ).map( apply( _ ) )
      def solve( term: LambdaExpression ): Boolean =
        images( term ) || ( term match {
          case Const( _, _ ) => true
          case App( a, b )   => solve( a ) && solve( b )
          case Var( _, _ )   => false
        } )
      !solve( map( x ) )
    }

}

object Substitution {
  def apply( subs: Traversable[( Var, LambdaExpression )], tySubs: Traversable[( TVar, Ty )] = Nil ): Substitution =
    new Substitution( Map() ++ subs, Map() ++ tySubs )
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
