package gapt.expr

import gapt.formats.babel.BabelExporter

sealed abstract class Ty {
  def ->:( that: Ty ) = TArr( that, this )

  override def toString =
    new BabelExporter( unicode = true, sig = implicitly ).export( this )
}
case class TBase( name: String, params: List[Ty] ) extends Ty
case class TArr( in: Ty, out: Ty ) extends Ty
case class TVar( name: String ) extends Ty

object TBase {

  /**
   * Creates a new base type.
   *
   * @param name The base type's name.
   * @param params The base type's type arguments.
   * @return A base type of the form (`name` `params`(0) ... `params`(n)),
   * where n is the length of `params`.
   */
  def apply( name: String, params: Ty* ): TBase = TBase( name, params.toList )
}

object ->: {

  /**
   * Interprets the given type as an arrow type.
   *
   * @param ty The type to be interpreted as an arrow type.
   * @return Returns Some( (t,r) ) if `ty` = t -> r, otherwise None is
   * returned.
   */
  def unapply( ty: Ty ): Option[( Ty, Ty )] =
    ty match {
      case TArr( a, b ) => Some( ( a, b ) )
      case _            => None
    }
}

object FunctionType {

  /**
   * Creates a function type.
   *
   * @param to The return type of the newly created function type.
   * @param from The argument types of the newly created function type.
   * @return A type of the form
   * `from(0)` -> ( `from(1)` -> ( ... (`from(n)` -> `to`)...)),
   * where n is the length of the sequence `from`
   */
  def apply( to: Ty, from: Seq[Ty] ): Ty = from.foldRight( to )( _ ->: _ )

  /**
   * Interprets the given type as function type.
   *
   * @param ty The type to be viewed as a function type.
   * @return Returns Some( (from, to) ) such that
   * `ty` = FunctionType(to, from).
   */
  def unapply( ty: Ty ): Option[( Ty, List[Ty] )] = ty match {
    case from ->: FunctionType( to, froms ) => Some( to, from :: froms )
    case _                                  => Some( ty, Nil )
  }
}

object arity {

  /**
   * Retrieves the arity of the given type.
   *
   * @param t The type whose arity is to be computed.
   * @return The arity of the functions represented by this type.
   */
  def apply( t: Ty ): Int = t match {
    case t1 ->: t2 => 1 + arity( t2 )
    case _         => 0
  }

  /**
   * Retrieves the expression's arity.
   *
   * @param e The expression whose arity is to be computed.
   * @return The arity of the given expression, that is, the arity of the
   * expression's type.
   */
  def apply( e: Expr ): Int = arity( e.ty )
}

object baseTypes {

  /**
   * Retrieves the base types occurring an a type.
   *
   * @param t The type whose base types are to be computed.
   * @return The set of base types occurring in type `t`.
   */
  def apply( t: Ty ): Set[TBase] = t match {
    case a ->: b            => apply( a ) union apply( b )
    case t @ TBase( _, ps ) => ps.view.flatMap( apply ).toSet + t
    case TVar( _ )          => Set()
  }
}

/**
 * This object represents the type of individuals.
 */
object Ti extends TBase( "i", List() )

/**
 * This object represents the type of truth values.
 */
object To extends TBase( "o", List() )
