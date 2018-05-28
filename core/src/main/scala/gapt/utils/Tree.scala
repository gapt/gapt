package gapt.utils

import gapt.expr.{ Expr, Replaceable, Substitutable, Substitution, VarOrConst }

case class Tree[+T]( value: T, children: Vector[Tree[T]] ) {
  def zip[S]( that: Tree[S] ): Tree[( T, S )] =
    Tree( ( this.value, that.value ), ( this.children, that.children ).zipped.map( _ zip _ ) )

  def map[S]( f: T => S ): Tree[S] =
    Tree( f( value ), children.map( _.map( f ) ) )

  def foreach( f: T => Unit ): Unit = {
    f( value )
    children.foreach( _.foreach( f ) )
  }

  def contains[S >: T]( t: S ): Boolean =
    value == t || children.exists( _.contains( t ) )

  def tails: Tree[Tree[T]] =
    Tree( this, children.map( _.tails ) )

  def postOrder: Vector[T] = {
    val out = Vector.newBuilder[T]
    def g( t: Tree[T] ): Unit = {
      t.children.foreach( g )
      out += t.value
    }
    g( this )
    out.result()
  }

  override def toString: String = {
    val out = new StringBuilder
    def p( t: Tree[T], n: Int ): Unit = {
      for ( _ <- 0 until n ) out += ' '
      out ++= t.value.toString
      out += '\n'
      for ( c <- t.children ) p( c, n + 2 )
    }
    p( this, 0 )
    out.result()
  }
}

object Tree {
  implicit def replaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Tree[I], Tree[O]] =
    new Replaceable[Tree[I], Tree[O]] {
      def replace( obj: Tree[I], p: PartialFunction[Expr, Expr] ): Tree[O] =
        obj.map( ev.replace( _, p ) )

      def names( obj: Tree[I] ): Set[VarOrConst] =
        obj.postOrder.view.flatMap( ev.names ).toSet
    }

  implicit def substitutable[S <: Substitution, I, O]( implicit ev: Substitutable[S, I, O] ): Substitutable[S, Tree[I], Tree[O]] =
    ( subst, tree ) => tree.map( ev.applySubstitution( subst, _ ) )
}
