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
  def reduce( normalizer: Normalizer, head: Expr, args: List[Expr] ): Option[( Expr, List[Expr] )]
}
object ReductionRule {
  def apply( rules: ReductionRule* ): ReductionRule = apply( rules )
  def apply( rules: Traversable[ReductionRule] ): ReductionRule = {
    val rules_ = rules.toList
    ( normalizer, head, args ) => rules_.view.flatMap( r => r.reduce( normalizer, head, args ) ).headOption
  }
}

class Normalizer( val rule: ReductionRule ) {
  def normalize( expr: Expr ): Expr = {
    val Apps( hd, as ) = expr
    val ( hd_, as_ ) = appWHNF( hd, as )
    Apps( hd_ match {
      case Abs.Block( xs, e ) if xs.nonEmpty =>
        Abs.Block( xs, normalize( e ) )
      case _ => hd_
    }, as_.map( normalize ) )
  }

  def whnf( expr: Expr ): Expr = {
    val Apps( hd, as ) = expr
    val ( hd_, as_ ) = appWHNF( hd, as )
    Apps( hd_, as_ )
  }

  def reduce1( expr: Expr ): Option[Expr] = {
    val Apps( hd, as ) = expr
    for ( ( hd_, as_ ) <- rule.reduce( this, hd, as ) )
      yield Apps( hd_, as_ )
  }

  def isDefEq( a: Expr, b: Expr ): Boolean =
    normalize( a ) == normalize( b )

  @tailrec
  final def appWHNF( hd: Expr, as: List[Expr] ): ( Expr, List[Expr] ) =
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
  def apply( rule: ReductionRule, expr: Expr ): Expr =
    new Normalizer( rule ).normalize( expr )

  def apply( expr: Expr )( implicit ctx: Context = Context.empty ): Expr = {
    val redRules = ctx.reductionRules.toVector
    apply( if ( redRules.isEmpty ) BetaReduction else ReductionRule( BetaReduction +: redRules ), expr )
  }
}

object BetaReduction extends ReductionRule {
  @tailrec
  def reduce( head: Expr, args: List[Expr], subst: Map[Var, Expr] = Map() ): Option[( Expr, List[Expr] )] =
    ( head, args ) match {
      case ( Abs( x, e ), a :: as ) =>
        reduce( e, as, subst + ( x -> a ) )
      case _ if subst.nonEmpty =>
        Some( Substitution( subst )( head ) -> args )
      case _ => None
    }

  override def reduce( normalizer: Normalizer, head: Expr, args: List[Expr] ): Option[( Expr, List[Expr] )] =
    if ( args.isEmpty )
      None
    else
      reduce( head, args )

  def betaNormalize( expression: Expr ): Expr =
    normalize( expression )

  def betaNormalize( f: Formula ): Formula =
    betaNormalize( f: Expr ).asInstanceOf[Formula]
}
