package gapt.grammars

import gapt.expr._
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables

import scala.collection.mutable

abstract class GeneralLeastGeneralGeneralization {
  def fast( a: Expr, b: Expr ): ( Expr, collection.Map[Var, Expr], collection.Map[Var, Expr] )

  def apply( as: Expr* ): ( Expr, Map[Expr, Substitution] ) =
    apply( as )

  def apply( as: Iterable[Expr] ): ( Expr, Map[Expr, Substitution] ) =
    apply( as.toList )

  def apply( as: List[Expr] ): ( Expr, Map[Expr, Substitution] ) =
    as match {
      case Nil      => throw new IllegalArgumentException( "Cannot compute lgg of empty list" )
      case a :: Nil => ( a, Map( a -> Substitution() ) )
      case a :: as_ =>
        val ( lgg_, substs_ ) = apply( as_ )
        val ( lgg, map_, mapA ) = fast( lgg_, a )
        val subst_ = Substitution( map_ )
        val substA = Substitution( mapA )
        ( lgg, Map() ++ substs_.view.mapValues( s_ => subst_.compose( s_ ).restrict( map_.keySet ) ).toMap + ( a -> substA ) )
    }
}

/**
 * Computes the minimum of two terms in the subsumption lattice,
 * together with the substitutions witnessing the subsumption.
 */
object leastGeneralGeneralization extends GeneralLeastGeneralGeneralization {
  def fast( a: Expr, b: Expr ): ( Expr, collection.Map[Var, Expr], collection.Map[Var, Expr] ) = {
    val lgg = new leastGeneralGeneralization
    ( lgg( a, b ), lgg.subst1, lgg.subst2 )
  }
}
class leastGeneralGeneralization {
  val vars = mutable.Map[( Expr, Expr ), Var]()
  val subst1 = mutable.Map[Var, Expr]()
  val subst2 = mutable.Map[Var, Expr]()

  var i = 0
  def apply( a: Expr, b: Expr ): Expr = {
    val Apps( fa, as ) = a
    val Apps( fb, bs ) = b
    if ( fa.isInstanceOf[Const] && fa == fb ) {
      fa( as.lazyZip( bs ).map { apply }: _* )
    } else {
      vars.getOrElseUpdate( a -> b, {
        i = i + 1
        val v = Var( s"x$i", a.ty )
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
object leastGeneralGeneralization1 extends GeneralLeastGeneralGeneralization {
  def fast( a: Expr, b: Expr ): ( Expr, collection.Map[Var, Expr], collection.Map[Var, Expr] ) = {
    def lgg( a: Expr, b: Expr ): ( Expr, Option[( Expr, Expr )] ) = {
      val Apps( fa, as ) = a
      val Apps( fb, bs ) = b
      if ( fa.isInstanceOf[Const] && fa == fb ) {
        val ( as_, s_ ) = as.lazyZip( bs ).map( lgg ).unzip
        if ( s_.flatten.distinct.size <= 1 ) {
          ( fa( as_ : _* ), s_.flatten.headOption )
        } else {
          ( Var( "x", a.ty ), Some( ( a, b ) ) )
        }
      } else {
        ( Var( "x", a.ty ), Some( ( a, b ) ) )
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
