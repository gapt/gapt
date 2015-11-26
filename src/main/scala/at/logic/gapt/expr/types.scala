package at.logic.gapt.expr

sealed abstract class Ty {
  def -> ( that: Ty ) = new -> ( this, that )
}
case class TBase( name: String ) extends Ty { override def toString = name }
case class -> ( in: Ty, out: Ty ) extends Ty { override def toString = s"($in -> $out)" }

/**
 * Function type from_0 -> (from_1 -> ... (from_n -> to)).
 */
object FunctionType {
  def apply( to: Ty, from: Seq[Ty] ): Ty = from.foldRight( to )( _ -> _ )
  def unapply( ty: Ty ): Option[( Ty, List[Ty] )] = ty match {
    case `->`( from, FunctionType( to, froms ) ) => Some( to, from :: froms )
    case _                                       => Some( ty, Nil )
  }
}

/**
 * Arity of a type.
 */
object arity {
  def apply( t: Ty ): Int = t match {
    case t1 -> t2 => 1 + arity( t2 )
    case _        => 0
  }

  def apply( e: LambdaExpression ): Int = arity( e.exptype )
}

/**
 * Base types occurring in a type.
 */
object baseTypes {
  def apply( t: Ty ): Set[TBase] = t match {
    case `->`( a, b ) => apply( a ) union apply( b )
    case t: TBase     => Set( t )
  }
}

object Ti extends TBase( "i" )
object To extends TBase( "o" )
