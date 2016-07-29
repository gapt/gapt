package at.logic.gapt.grammars

import at.logic.gapt.expr.{ Apps, Const, LambdaExpression, Substitution, Var, freeVariables }

import scala.collection.mutable

/**
 * Computes the minimum of two terms in the subsumption lattice,
 * together with the substitutions witnessing the subsumption.
 */
object leastGeneralGeneralization {
  def apply( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    val lgg = new leastGeneralGeneralization
    ( lgg( a, b ), lgg.subst1, lgg.subst2 )
  }
  def apply( a: Seq[LambdaExpression], b: Seq[LambdaExpression] ): ( Seq[LambdaExpression], collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    val lgg = new leastGeneralGeneralization
    ( ( a, b ).zipped.map( lgg.apply ), lgg.subst1, lgg.subst2 )
  }
}
class leastGeneralGeneralization {
  val vars = mutable.Map[( LambdaExpression, LambdaExpression ), Var]()
  val subst1 = mutable.Map[Var, LambdaExpression]()
  val subst2 = mutable.Map[Var, LambdaExpression]()

  var i = 0
  def apply( a: LambdaExpression, b: LambdaExpression ): LambdaExpression = {
    val Apps( fa, as ) = a
    val Apps( fb, bs ) = b
    if ( fa.isInstanceOf[Const] && fa == fb ) {
      fa( ( as, bs ).zipped map apply: _* )
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
}

/**
 * Computes the minimum of two terms in the subsumption lattice of
 * terms with at most one free variable, together with the substitutions
 * witnessing the subsumption.
 */
object leastGeneralGeneralization1 {
  def apply( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, collection.Map[Var, LambdaExpression], collection.Map[Var, LambdaExpression] ) = {
    def lgg( a: LambdaExpression, b: LambdaExpression ): ( LambdaExpression, Option[( LambdaExpression, LambdaExpression )] ) = {
      val Apps( fa, as ) = a
      val Apps( fb, bs ) = b
      if ( fa.isInstanceOf[Const] && fa == fb ) {
        val ( as_, s_ ) = ( as, bs ).zipped.map( lgg ).unzip
        if ( s_.flatten.distinct.size <= 1 ) {
          ( fa( as_ : _* ), s_.flatten.headOption )
        } else {
          ( Var( "x", a.exptype ), Some( ( a, b ) ) )
        }
      } else {
        ( Var( "x", a.exptype ), Some( ( a, b ) ) )
      }
    }

    lgg( a, b ) match {
      case ( au1, None ) => ( au1, Map(), Map() )
      case ( au1, Some( ( substA, substB ) ) ) =>
        val v = freeVariables( au1 ).head
        ( au1, Map( v -> substA ), Map( v -> substB ) )
    }
  }
}
