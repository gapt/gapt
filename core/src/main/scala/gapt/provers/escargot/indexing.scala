package gapt.provers.escargot.impl
import DiscrTree._
import gapt.expr._

class TermString( private val stack: List[Any] ) extends AnyVal {
  def isEmpty: Boolean = stack.isEmpty
  def jump: TermString = new TermString( stack.tail )
  def next: Option[( Label, TermString )] =
    stack match {
      case Nil => None
      case TBase( n, as ) :: rest =>
        Some( ( Constant( n, as.length ), new TermString( as ++ rest ) ) )
      case TVar( _ ) :: rest =>
        Some( ( Variable, new TermString( rest ) ) )
      case ( a ->: b ) :: rest =>
        Some( ( Constant( "->", 2 ), new TermString( a :: b :: rest ) ) )
      case Apps( hd, as ) :: rest =>
        Some( hd match {
          case Const( n, _, _ ) => ( Constant( n, as.length ), new TermString( as ++ rest ) )
          case _                => ( Variable, new TermString( rest ) )
        } )
    }
  def toList: List[Label] =
    next match {
      case None               => Nil
      case Some( ( hd, tl ) ) => hd :: tl.toList
    }
}
object TermString {
  def apply( e: Expr ): TermString = new TermString( e.ty :: e :: Nil )
}

sealed trait DiscrTree[T] {
  def isEmpty: Boolean =
    this match {
      case Leaf( elems ) => elems.isEmpty
      case Node( next )  => next.values.forall( _.isEmpty )
    }

  def filter( p: T => Boolean ): DiscrTree[T] =
    this match {
      case Leaf( elems ) => Leaf( elems.filter( p ) )
      case Node( next )  => Node( Map() ++ next.mapValues( _.filter( p ) ) )
    }

  def remove( t: T ): DiscrTree[T] = filter( _ != t )

  def jump( n: Int = 1 ): Vector[DiscrTree[T]] = {
    val result = Vector.newBuilder[DiscrTree[T]]
    def walk( t: DiscrTree[T], n: Int ): Unit =
      t match {
        case _ if n == 0 =>
          result += t
        case Leaf( _ ) =>
        case Node( next ) =>
          for ( ( l, ch ) <- next )
            walk( ch, n - 1 + l.arity )
      }
    walk( this, n )
    result.result()
  }

  def foreach( f: T => Unit ): Unit =
    this match {
      case Leaf( elems ) => elems.foreach( f )
      case Node( next )  => next.values.foreach( _.foreach( f ) )
    }

  def elements: Vector[T] = {
    val builder = Vector.newBuilder[T]
    foreach( builder += _ )
    builder.result()
  }

  def insert( es: Iterable[( Expr, T )] ): DiscrTree[T] =
    es.foldLeft( this ) { case ( dt, ( e, t ) ) => dt.insert( e, t ) }
  def insert( es: Iterable[Expr], t: T ): DiscrTree[T] =
    es.foldLeft( this )( _.insert( _, t ) )
  def insert( e: Expr, t: T ): DiscrTree[T] = insert( TermString( e ), t )
  def insert( e: TermString, t: T ): DiscrTree[T] =
    ( e.next, this ) match {
      case ( None, Leaf( elems ) ) => Leaf( elems :+ t )
      case ( Some( ( label, e_ ) ), Node( next ) ) =>
        Node( next.updated(
          label,
          next.getOrElse( label, if ( e_.isEmpty ) Leaf[T]( Vector.empty ) else Node[T]( Map() ) ).
            insert( e_, t ) ) )
      case _ =>
        throw new IllegalStateException
    }

  def generalizations( e: Expr ): Vector[T] = generalizations( TermString( e ) )
  def generalizations( e: TermString ): Vector[T] =
    ( e.next, this ) match {
      case ( None, Leaf( elems ) ) => elems
      case ( Some( ( label, e_ ) ), Node( next ) ) =>
        val res1 = next.get( Variable ).map( _.generalizations( e.jump ) ).getOrElse( Vector.empty[T] )
        if ( label == Variable ) res1 else
          res1 ++ next.get( label ).map( _.generalizations( e_ ) ).getOrElse( Vector.empty[T] )
      case _ =>
        throw new IllegalStateException
    }

  def unifiable( e: Expr ): Vector[T] = unifiable( TermString( e ) )
  def unifiable( e: TermString ): Vector[T] =
    ( e.next, this ) match {
      case ( None, Leaf( elems ) ) => elems
      case ( Some( ( label, e_ ) ), Node( next ) ) =>
        if ( label == Variable )
          jump().view.flatMap( _.unifiable( e_ ) ).toVector
        else
          next.get( Variable ).map( _.unifiable( e.jump ) ).getOrElse( Vector.empty[T] ) ++
            next.get( label ).map( _.unifiable( e_ ) ).getOrElse( Vector.empty[T] )
      case _ =>
        throw new IllegalStateException
    }

}

object DiscrTree {
  sealed trait Label {
    def arity: Int
  }
  case object Variable extends Label { def arity = 0 }
  case class Constant( n: String, arity: Int ) extends Label

  case class Leaf[T]( elems: Vector[T] ) extends DiscrTree[T]
  case class Node[T]( next: Map[Label, DiscrTree[T]] ) extends DiscrTree[T]

  private val empty: DiscrTree[Any] = Node( Map() )
  def apply[T](): DiscrTree[T] = empty.asInstanceOf[DiscrTree[T]]
}