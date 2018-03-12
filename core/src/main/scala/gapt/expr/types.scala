package gapt.expr

import gapt.formats.babel.BabelExporter

sealed abstract class Ty {
  def ->:( that: Ty ) = TArr( that, this )

  override def toString = new BabelExporter( unicode = true, sig = implicitly ).export( this )
}
case class TBase( name: String, params: List[Ty] ) extends Ty
case class TArr( in: Ty, out: Ty ) extends Ty
case class TVar( name: String ) extends Ty

object TBase {
  def apply( name: String, params: Ty* ): TBase = TBase( name, params.toList )
}
object ->: {
  def unapply( ty: Ty ): Option[( Ty, Ty )] =
    ty match {
      case TArr( a, b ) => Some( ( a, b ) )
      case _            => None
    }
}

/**
 * Function type from_0 -> (from_1 -> ... (from_n -> to)).
 */
object FunctionType {
  def apply( to: Ty, from: Seq[Ty] ): Ty = from.foldRight( to )( _ ->: _ )
  def unapply( ty: Ty ): Option[( Ty, List[Ty] )] = ty match {
    case from ->: FunctionType( to, froms ) => Some( to, from :: froms )
    case _                                  => Some( ty, Nil )
  }
}

/**
 * Arity of a type.
 */
object arity {
  def apply( t: Ty ): Int = t match {
    case t1 ->: t2 => 1 + arity( t2 )
    case _         => 0
  }

  def apply( e: Expr ): Int = arity( e.ty )
}

/**
 * Base types occurring in a type.
 */
object baseTypes {
  def apply( t: Ty ): Set[TBase] = t match {
    case a ->: b            => apply( a ) union apply( b )
    case t @ TBase( _, ps ) => ps.view.flatMap( apply ).toSet + t
    case TVar( _ )          => Set()
  }
}

object Ti extends TBase( "i", List() )
object To extends TBase( "o", List() )
