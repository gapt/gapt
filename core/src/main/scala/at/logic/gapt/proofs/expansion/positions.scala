package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, instantiate }

private object getAtHOLPosition {
  def apply( et: ExpansionTree, pos: HOLPosition ): Set[ExpansionTree] =
    if ( pos.isEmpty ) Set( et ) else ( et, pos.head ) match {
      case ( ETMerge( a, b ), _ )                   => apply( a, pos ) union apply( b, pos )

      case ( ETNeg( ch ), 1 )                       => apply( ch, pos.tail )

      case ( ETAnd( l, _ ), 1 )                     => apply( l, pos.tail )
      case ( ETAnd( _, r ), 2 )                     => apply( r, pos.tail )

      case ( ETOr( l, _ ), 1 )                      => apply( l, pos.tail )
      case ( ETOr( _, r ), 2 )                      => apply( r, pos.tail )

      case ( ETImp( l, _ ), 1 )                     => apply( l, pos.tail )
      case ( ETImp( _, r ), 2 )                     => apply( r, pos.tail )

      case ( ETStrongQuantifier( _, _, ch ), 1 )    => apply( ch, pos.tail )
      case ( ETSkolemQuantifier( _, _, _, ch ), 1 ) => apply( ch, pos.tail )
      case ( ETWeakQuantifier( _, insts ), 1 )      => insts.values flatMap { apply( _, pos.tail ) } toSet

      case ( _, _ )                                 => Set()
    }
}

object replaceAtHOLPosition {
  def apply( et: ExpansionTree, pos: HOLPosition, exp: LambdaExpression ): ExpansionTree = {
    val rest = pos.tail
    ( et, pos.head ) match {
      case ( ETMerge( left, right ), _ )                => ETMerge( replaceAtHOLPosition( left, pos, exp ), replaceAtHOLPosition( right, pos, exp ) )

      case ( ETTop( _ ), _ ) | ( ETBottom( _ ), _ )     => et
      case ( ETAtom( formula, polarity ), _ )           => ETAtom( formula.replace( pos, exp ).asInstanceOf[HOLAtom], polarity )
      case ( et @ ETDefinedAtom( atom, _, _ ), _ )      => et.copy( atom = atom.replace( pos, exp ).asInstanceOf[HOLAtom] )

      case ( ETWeakening( formula, polarity ), _ )      => ETWeakening( formula.replace( pos, exp ), polarity )

      case ( ETNeg( sub ), 1 )                          => ETNeg( replaceAtHOLPosition( sub, rest, exp ) )

      case ( ETAnd( left, right ), 1 )                  => ETAnd( replaceAtHOLPosition( left, rest, exp ), right )
      case ( ETAnd( left, right ), 2 )                  => ETAnd( left, replaceAtHOLPosition( right, rest, exp ) )

      case ( ETOr( left, right ), 1 )                   => ETOr( replaceAtHOLPosition( left, rest, exp ), right )
      case ( ETOr( left, right ), 2 )                   => ETOr( left, replaceAtHOLPosition( right, rest, exp ) )

      case ( ETImp( left, right ), 1 )                  => ETImp( replaceAtHOLPosition( left, rest, exp ), right )
      case ( ETImp( left, right ), 2 )                  => ETImp( left, replaceAtHOLPosition( right, rest, exp ) )

      //FIXME: Quantifier cases are not entirely safe: What if the eigenvariable or the instances are replaced?
      case ( ETStrongQuantifier( formula, v, sub ), 1 ) => ETStrongQuantifier( formula.replace( pos, exp ), v, replaceAtHOLPosition( sub, rest, exp ) )
      case ( ETSkolemQuantifier( formula, skt, skf, sub ), 1 ) =>
        ETSkolemQuantifier( formula.replace( pos, exp ), skt, skf, replaceAtHOLPosition( sub, rest, exp ) )

      case ( ETWeakQuantifier( formula, instances ), 1 ) =>
        ETWeakQuantifier(
          formula.replace( pos, exp ),
          for ( ( term, instance ) <- instances )
            yield term -> replaceAtHOLPosition( instance, rest, exp )
        )
    }
  }
}

/**
 * Replaces terms in an expansion tree according to a replacement context.
 */
object replaceWithContext {
  /**
   * Instantiates the quantifier inside a replacement context.
   *
   * Given λx ∀y P(x,y) and f(c), it will return λx P(x,f(c)).
   */
  private def instReplCtx( ctx: Abs, term: LambdaExpression ): Abs =
    ctx match {
      case Abs( x, quantFormula ) if freeVariables( term ) contains x =>
        val newX = rename( x, freeVariables( term ) )
        instReplCtx( Abs( newX, Substitution( x -> newX )( quantFormula ) ), term )
      case Abs( x, quantFormula: HOLFormula ) =>
        Abs( x, instantiate( quantFormula, term ) )
    }

  /**
   *
   * @param et An expansion tree.
   * @param replacementContext A replacement context, i.e. a lambda expression of the form λx.E.
   * @param exp The term to insert for x.
   * @return A new expansion tree where x has been replaced with exp in every node.
   */
  def apply( et: ExpansionTree, replacementContext: Abs, exp: LambdaExpression ): ExpansionTree = {
    def newFormula = BetaReduction.betaNormalize( App( replacementContext, exp ) ).asInstanceOf[HOLFormula]
    def newAtom = newFormula.asInstanceOf[HOLAtom]

    ( et, replacementContext ) match {
      case ( ETMerge( left, right ), _ )                   => ETMerge( apply( left, replacementContext, exp ), apply( right, replacementContext, exp ) )
      case ( ETTop( _ ), _ ) | ( ETBottom( _ ), _ )        => et
      case ( et @ ETAtom( formula, _ ), _ )                => et.copy( atom = newAtom )
      case ( et @ ETDefinedAtom( atom, _, _ ), _ )         => et.copy( atom = newAtom )
      case ( et @ ETWeakening( formula, _ ), _ )           => et.copy( formula = newFormula )
      case ( ETNeg( sub ), Abs( v, Neg( f ) ) )            => ETNeg( apply( sub, Abs( v, f ), exp ) )
      case ( ETAnd( left, right ), Abs( v, And( l, r ) ) ) => ETAnd( apply( left, Abs( v, l ), exp ), apply( right, Abs( v, r ), exp ) )
      case ( ETOr( left, right ), Abs( v, Or( l, r ) ) )   => ETOr( apply( left, Abs( v, l ), exp ), apply( right, Abs( v, r ), exp ) )
      case ( ETImp( left, right ), Abs( v, Imp( l, r ) ) ) => ETImp( apply( left, Abs( v, l ), exp ), apply( right, Abs( v, r ), exp ) )
      case ( ETStrongQuantifier( formula, x, sub ), _ ) =>
        ETStrongQuantifier( newFormula, x, apply( sub, instReplCtx( replacementContext, x ), exp ) )
      case ( ETSkolemQuantifier( formula, skTerm, skDef, sub ), _ ) =>
        ETSkolemQuantifier( newFormula, skTerm, skDef, apply( sub, instReplCtx( replacementContext, skTerm ), exp ) )
      case ( ETWeakQuantifier( formula, instances ), _ ) =>
        ETWeakQuantifier(
          newFormula,
          for ( ( term, instance ) <- instances )
            yield term -> apply( instance, instReplCtx( replacementContext, term ), exp )
        )
      case _ => throw new IllegalArgumentException( s"Tree $et and context $replacementContext could not be handled." )
    }
  }
}

object generalizeET {
  def apply( et: ExpansionTree, newShallow: HOLFormula ): ExpansionTree =
    HOLPosition.differingPositions( et.shallow, newShallow ).foldLeft( et )( ( et_, pos ) =>
      replaceAtHOLPosition( et_, pos, newShallow( pos ) ) )
}

