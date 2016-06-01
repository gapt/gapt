
package at.logic.gapt.expr

import at.logic.gapt.proofs.Sequent

trait Replaceable[-I, +O] {
  def replace( obj: I, p: PartialFunction[LambdaExpression, LambdaExpression] ): O
}
trait ClosedUnderReplacement[T] extends Replaceable[T, T]

private[expr] trait DefaultReplaceables {

  private object lambdaExpressionReplacer extends ClosedUnderReplacement[LambdaExpression] {
    def replace( term: LambdaExpression, map: PartialFunction[LambdaExpression, LambdaExpression] ): LambdaExpression =
      term match {
        case _ if map isDefinedAt term => map( term )

        // special case polymorphic constants so that we can do type-changing replacements
        // but only if the user doesn't specify any replacement for the logical constants
        case Eq( s, t ) if !( map isDefinedAt EqC( s.exptype ) ) =>
          Eq( replace( s, map ), replace( t, map ) )
        case All( x, t ) if !( map isDefinedAt ForallC( x.exptype ) ) =>
          All( replace( x, map ).asInstanceOf[Var], replace( t, map ) )
        case Ex( x, t ) if !( map isDefinedAt ExistsC( x.exptype ) ) =>
          Ex( replace( x, map ).asInstanceOf[Var], replace( t, map ) )

        case App( s, t ) =>
          App( replace( s, map ), replace( t, map ) )
        case Abs( x, t ) =>
          Abs( replace( x, map ).asInstanceOf[Var], replace( t, map ) )

        case _ => term
      }
  }
  private object holFormulaReplacer extends ClosedUnderReplacement[HOLFormula] {
    override def replace( obj: HOLFormula, p: PartialFunction[LambdaExpression, LambdaExpression] ): HOLFormula =
      lambdaExpressionReplacer.replace( obj, p ).asInstanceOf[HOLFormula]
  }

  implicit def lambdaExpressionReplaceable[I <: LambdaExpression]( implicit notAFormula: Not[I <:< HOLFormula] ): Replaceable[I, LambdaExpression] = lambdaExpressionReplacer
  implicit def holFormulaReplaceable[I <: HOLFormula]( implicit notAnAtom: Not[I <:< HOLAtom] ): Replaceable[I, HOLFormula] = holFormulaReplacer
  implicit object holAtomReplaceable extends ClosedUnderReplacement[HOLAtom] {
    override def replace( obj: HOLAtom, p: PartialFunction[LambdaExpression, LambdaExpression] ): HOLAtom =
      lambdaExpressionReplacer.replace( obj, p ).asInstanceOf[HOLAtom]
  }

  implicit object substitutionReplaceable extends ClosedUnderReplacement[Substitution] {
    def replace( subst: Substitution, p: PartialFunction[LambdaExpression, LambdaExpression] ): Substitution =
      Substitution( for ( ( l, r ) <- subst.map ) yield TermReplacement( l, p ).asInstanceOf[Var] -> TermReplacement( r, p ) )
  }

  implicit def sequentReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Sequent[I], Sequent[O]] =
    new Replaceable[Sequent[I], Sequent[O]] {
      override def replace( obj: Sequent[I], p: PartialFunction[LambdaExpression, LambdaExpression] ) =
        obj.map { TermReplacement( _, p ) }
    }

  implicit def tupleReplaceable[I1, I2, O1, O2]( implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2] ): Replaceable[( I1, I2 ), ( O1, O2 )] =
    new Replaceable[( I1, I2 ), ( O1, O2 )] {
      override def replace( obj: ( I1, I2 ), p: PartialFunction[LambdaExpression, LambdaExpression] ): ( O1, O2 ) =
        ( ev1.replace( obj._1, p ), ev2.replace( obj._2, p ) )
    }

}

/**
 * A term replacement homomorphically extends a partial function on lambda expressions to all lambda expressions.
 *
 * This is done on a "best effort" basis.  Replacing constants by ground terms of the same type will usually work, anything beyond that might or might not work.
 */
object TermReplacement {
  def apply( term: LambdaExpression, what: LambdaExpression, by: LambdaExpression ): LambdaExpression =
    apply( term, Map( what -> by ) )

  def apply( f: HOLFormula, what: LambdaExpression, by: LambdaExpression ): HOLFormula =
    apply( f, Map( what -> by ) )

  def apply[I, O]( obj: I, p: PartialFunction[LambdaExpression, LambdaExpression] )( implicit ev: Replaceable[I, O] ): O =
    ev.replace( obj, p )
}

