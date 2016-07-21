
package at.logic.gapt.expr

import at.logic.gapt.proofs.Sequent

trait Replaceable[-I, +O] {
  def replace( obj: I, p: PartialFunction[LambdaExpression, LambdaExpression] ): O

  def names( obj: I ): Set[VarOrConst]
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

    def names( term: LambdaExpression ): Set[VarOrConst] =
      constants( term ).toSet[VarOrConst] union variables( term ).toSet
  }
  private object holFormulaReplacer extends ClosedUnderReplacement[HOLFormula] {
    override def replace( obj: HOLFormula, p: PartialFunction[LambdaExpression, LambdaExpression] ): HOLFormula =
      lambdaExpressionReplacer.replace( obj, p ).asInstanceOf[HOLFormula]

    def names( obj: HOLFormula ) = lambdaExpressionReplacer.names( obj )
  }

  implicit def lambdaExpressionReplaceable[I <: LambdaExpression]( implicit notAFormula: Not[I <:< HOLFormula] ): Replaceable[I, LambdaExpression] = lambdaExpressionReplacer
  implicit def holFormulaReplaceable[I <: HOLFormula]( implicit notAnAtom: Not[I <:< HOLAtom] ): Replaceable[I, HOLFormula] = holFormulaReplacer
  implicit object holAtomReplaceable extends ClosedUnderReplacement[HOLAtom] {
    override def replace( obj: HOLAtom, p: PartialFunction[LambdaExpression, LambdaExpression] ): HOLAtom =
      lambdaExpressionReplacer.replace( obj, p ).asInstanceOf[HOLAtom]

    def names( obj: HOLAtom ) = lambdaExpressionReplacer.names( obj )
  }

  implicit object substitutionReplaceable extends ClosedUnderReplacement[Substitution] {
    def replace( subst: Substitution, p: PartialFunction[LambdaExpression, LambdaExpression] ): Substitution =
      Substitution( for ( ( l, r ) <- subst.map ) yield TermReplacement( l, p ).asInstanceOf[Var] -> TermReplacement( r, p ) )

    def names( obj: Substitution ) =
      obj.map.keySet ++ obj.map.values flatMap { containedNames( _ ) }
  }

  implicit def sequentReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Sequent[I], Sequent[O]] =
    new Replaceable[Sequent[I], Sequent[O]] {
      override def replace( obj: Sequent[I], p: PartialFunction[LambdaExpression, LambdaExpression] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Sequent[I] ) = obj.elements flatMap { containedNames( _ ) } toSet
    }

  implicit def seqReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Seq[I], Seq[O]] =
    new Replaceable[Seq[I], Seq[O]] {
      override def replace( obj: Seq[I], p: PartialFunction[LambdaExpression, LambdaExpression] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Seq[I] ) = obj flatMap { containedNames( _ ) } toSet
    }

  implicit def setReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Set[I], Set[O]] =
    new Replaceable[Set[I], Set[O]] {
      override def replace( obj: Set[I], p: PartialFunction[LambdaExpression, LambdaExpression] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Set[I] ) = obj flatMap { containedNames( _ ) }
    }

  implicit def optionReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Option[I], Option[O]] =
    new Replaceable[Option[I], Option[O]] {
      override def replace( obj: Option[I], p: PartialFunction[LambdaExpression, LambdaExpression] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Option[I] ) = obj.toSet[I] flatMap { containedNames( _ ) }
    }

  implicit def tupleReplaceable[I1, I2, O1, O2]( implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2] ): Replaceable[( I1, I2 ), ( O1, O2 )] =
    new Replaceable[( I1, I2 ), ( O1, O2 )] {
      override def replace( obj: ( I1, I2 ), p: PartialFunction[LambdaExpression, LambdaExpression] ): ( O1, O2 ) =
        ( ev1.replace( obj._1, p ), ev2.replace( obj._2, p ) )

      def names( obj: ( I1, I2 ) ) = containedNames( obj._1 ) union containedNames( obj._2 )
    }

  implicit def mapReplaceable[I1, I2, O1, O2]( implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2] ): Replaceable[Map[I1, I2], Map[O1, O2]] =
    new Replaceable[Map[I1, I2], Map[O1, O2]] {
      override def replace( obj: Map[I1, I2], p: PartialFunction[LambdaExpression, LambdaExpression] ): Map[O1, O2] =
        obj.map( TermReplacement( _, p ) )

      def names( obj: Map[I1, I2] ) = containedNames( obj.toSeq )
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

  /**
   * Performs capture-avoiding term replacement.
   *
   * If a constant or variable occurs both in the range of partialMap
   * and obj, we rename the occurrence in obj first to something else.
   */
  def hygienic[I, O]( obj: I, partialMap: Map[Const, LambdaExpression] )( implicit ev: Replaceable[I, O] ): O = {
    val namesInObj = containedNames( obj )
    val namesInRange = partialMap.values.flatMap { containedNames( _ ) }.toSet

    val needToRename = namesInObj intersect namesInRange -- partialMap.keySet
    val nameGen = rename.awayFrom( namesInObj ++ namesInRange ++ partialMap.keySet )
    val renaming = for ( n <- needToRename ) yield n -> nameGen.fresh( n )

    TermReplacement( obj, partialMap ++ renaming toMap )
  }
}

object containedNames {
  def apply[I, O]( obj: I )( implicit ev: Replaceable[I, O] ): Set[VarOrConst] =
    ev.names( obj )
}

