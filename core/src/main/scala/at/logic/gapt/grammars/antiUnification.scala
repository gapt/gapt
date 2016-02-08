package at.logic.gapt.grammars

import at.logic.gapt.expr.{ freeVariables, Apps, Var, LambdaExpression }

import scala.collection.mutable

object antiUnifier {
  def apply( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    val vars = mutable.Map[( LambdaExpression, LambdaExpression ), Var]()
    val subst1 = mutable.Map[Var, LambdaExpression]()
    val subst2 = mutable.Map[Var, LambdaExpression]()

    var i = 0
    def au( a: LambdaExpression, b: LambdaExpression ): LambdaExpression = {
      val Apps( fa, as ) = a
      val Apps( fb, bs ) = b
      if ( fa == fb ) {
        fa( ( as, bs ).zipped map au: _* )
      } else {
        vars.getOrElseUpdate( a -> b, {
          i = i + 1
          val v = Var( s"x$i", a.exptype )
          subst1( v ) = a
          subst2( v ) = b
          v
        } )
      }
    }

    ( au( a, b ), subst1, subst2 )
  }
}

object antiUnifier1 {

  def apply( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    def au( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, Option[( LambdaExpression, LambdaExpression )] ) = {
      val Apps( fa, as ) = a
      val Apps( fb, bs ) = b
      if ( fa == fb ) {
        val ( as_, s_ ) = ( as, bs ).zipped.map( au ).unzip
        if ( s_.flatten.distinct.size <= 1 ) {
          ( fa( as_ : _* ), s_.flatten.headOption )
        } else {
          ( Var( "x", a.exptype ), Some( ( a, b ) ) )
        }
      } else {
        ( Var( "x", a.exptype ), Some( ( a, b ) ) )
      }
    }

    au( a, b ) match {
      case ( au1, None ) => ( au1, Map(), Map() )
      case ( au1, Some( ( substA, substB ) ) ) =>
        val v = freeVariables( au1 ).head
        ( au1, Map( v -> substA ), Map( v -> substB ) )
    }
  }
}
