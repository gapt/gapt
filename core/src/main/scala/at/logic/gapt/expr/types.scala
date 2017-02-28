package at.logic.gapt.expr

import at.logic.gapt.formats.babel.BabelExporter

sealed abstract class Ty {
  def -> ( that: Ty ) = new -> ( this, that )

  override def toString = new BabelExporter( unicode = true, sig = implicitly ).export( this )
}
case class TBase( name: String ) extends Ty
case class -> ( in: Ty, out: Ty ) extends Ty
case class TVar( name: String ) extends Ty

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
    case TVar( _ )    => Set()
  }
}

object typeMatching {
  def apply( a: Ty, b: Ty ): Option[Map[TVar, Ty]] =
    apply( List( ( a, b ) ), Map[TVar, Ty]() )

  def apply( pairs: List[( Ty, Ty )], alreadyFixedSubst: Map[TVar, Ty] ): Option[Map[TVar, Ty]] =
    pairs match {
      case Nil => Some( alreadyFixedSubst )
      case first :: rest =>
        first match {
          case ( TBase( n ), TBase( n_ ) ) if n == n_ => apply( rest, alreadyFixedSubst )
          case ( a1 -> b1, a2 -> b2 ) => apply( ( a1, a2 ) :: ( b1, b2 ) :: rest, alreadyFixedSubst )
          case ( v: TVar, t ) if !alreadyFixedSubst.contains( v ) => apply( rest, alreadyFixedSubst.updated( v, t ) )
          case ( v: TVar, t ) if alreadyFixedSubst.get( v ).contains( t ) => apply( rest, alreadyFixedSubst )
          case _ => None
        }
    }
}

object Ti extends TBase( "i" )
object To extends TBase( "o" )
