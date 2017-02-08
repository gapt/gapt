package at.logic.gapt.expr

import at.logic.gapt.proofs.Context

import scala.annotation.tailrec

/**
 * Expression-level reduction rule.
 *
 * Examples are beta-reduction in [[BetaReduction]], and delta-reduction in [[Context.Definitions]].
 */
trait ReductionRule {
  /** Performs a one-step reduction of head(args: _*). */
  def reduce( normalizer: Normalizer, head: LambdaExpression, args: List[LambdaExpression] ): Option[( LambdaExpression, List[LambdaExpression] )]
}
object ReductionRule {
  def apply( rules: ReductionRule* ): ReductionRule = apply( rules )
  def apply( rules: Traversable[ReductionRule] ): ReductionRule = {
    val rules_ = rules.toList
    ( normalizer, head, args ) => rules_.view.flatMap( r => r.reduce( normalizer, head, args ) ).headOption
  }
}

class Normalizer( rule: ReductionRule ) {
  def normalize( expr: LambdaExpression ): LambdaExpression = {
    val Apps( hd, as ) = expr
    val ( hd_, as_ ) = appWHNF( hd, as )
    Apps( hd_ match {
      case Abs.Block( xs, e ) if xs.nonEmpty =>
        Abs.Block( xs, normalize( e ) )
      case _ => hd_
    }, as_.map( normalize ) )
  }

  def whnf( expr: LambdaExpression ): LambdaExpression = {
    val Apps( hd, as ) = expr
    val ( hd_, as_ ) = appWHNF( hd, as )
    Apps( hd_, as_ )
  }

  def isDefEq( a: LambdaExpression, b: LambdaExpression ): Boolean =
    normalize( a ) == normalize( b )

  @tailrec
  final def appWHNF( hd: LambdaExpression, as: List[LambdaExpression] ): ( LambdaExpression, List[LambdaExpression] ) =
    rule.reduce( this, hd, as ) match {
      case Some( ( Apps( hd_, as__ ), as_ ) ) =>
        if ( as__.isEmpty )
          appWHNF( hd_, as_ )
        else
          appWHNF( hd_, as__ ++: as_ )
      case None =>
        ( hd, as )
    }
}

object normalize {
  def apply( rule: ReductionRule, expr: LambdaExpression ): LambdaExpression =
    new Normalizer( rule ).normalize( expr )

  def apply( expr: LambdaExpression )( implicit ctx: Context = Context.empty ): LambdaExpression = {
    val redRules = ctx.reductionRules.toVector
    apply( if ( redRules.isEmpty ) BetaReduction else ReductionRule( BetaReduction +: redRules ), expr )
  }
}

object BetaReduction extends ReductionRule {
  @tailrec
  def reduce( head: LambdaExpression, args: List[LambdaExpression], subst: Map[Var, LambdaExpression] = Map() ): Option[( LambdaExpression, List[LambdaExpression] )] =
    ( head, args ) match {
      case ( Abs( x, e ), a :: as ) =>
        reduce( e, as, subst + ( x -> a ) )
      case _ if subst.nonEmpty =>
        Some( Substitution( subst )( head ) -> args )
      case _ => None
    }

  override def reduce( normalizer: Normalizer, head: LambdaExpression, args: List[LambdaExpression] ): Option[( LambdaExpression, List[LambdaExpression] )] =
    if ( args.isEmpty )
      None
    else
      reduce( head, args )

  def betaNormalize( expression: LambdaExpression ): LambdaExpression =
    normalize( expression )

  def betaNormalize( f: HOLFormula ): HOLFormula =
    betaNormalize( f: LambdaExpression ).asInstanceOf[HOLFormula]
}
