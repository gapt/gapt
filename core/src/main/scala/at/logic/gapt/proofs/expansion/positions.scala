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
  def apply( et: ExpansionTree, pos: HOLPosition, exp: LambdaExpression ): ExpansionTree =
    replaceWithContext( et, replacementContext( et.shallow( pos ).exptype, et.shallow, Some( pos ) ), exp )
}

/**
 * Replaces terms in an expansion tree according to a replacement context.
 */
object replaceWithContext {
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
      case ( et @ ETWeakening( formula, _ ), _ )           => et.copy( formula = newFormula )
      case ( ETNeg( sub ), Abs( v, Neg( f ) ) )            => ETNeg( apply( sub, Abs( v, f ), exp ) )
      case ( ETAnd( left, right ), Abs( v, And( l, r ) ) ) => ETAnd( apply( left, Abs( v, l ), exp ), apply( right, Abs( v, r ), exp ) )
      case ( ETOr( left, right ), Abs( v, Or( l, r ) ) )   => ETOr( apply( left, Abs( v, l ), exp ), apply( right, Abs( v, r ), exp ) )
      case ( ETImp( left, right ), Abs( v, Imp( l, r ) ) ) => ETImp( apply( left, Abs( v, l ), exp ), apply( right, Abs( v, r ), exp ) )
      case ( ETStrongQuantifier( formula, x, sub ), _ ) =>
        ETStrongQuantifier( newFormula, x, apply( sub, instReplCtx( replacementContext, x ), exp ) )

      case ( ETSkolemQuantifier( formula, skTerm @ Apps( skConst, skArgs ), skDef, sub ), _ ) =>
        val boundVars = freeVariables( formula ) ++ freeVariables( skTerm ) ++ freeVariables( exp )
        val nameGen = rename.awayFrom( boundVars )

        val newSkArgs = skArgs.map( a => nameGen.fresh( Var( "x", a.exptype ) ) )
        val lhs = newFormula
        val rhs = BetaReduction.betaNormalize( skDef( newSkArgs ) )
        val subst = syntacticMGU( lhs, rhs, boundVars ).
          getOrElse( throw new IllegalArgumentException( s"Cannot unify $lhs =?= $rhs" ) )
        val newSkTerm = subst( skConst( newSkArgs ) )

        ETSkolemQuantifier( newFormula, newSkTerm, skDef, apply( sub, instReplCtx( replacementContext, newSkTerm ), exp ) )

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

/**
 * Inserts a definition into an expansion tree by either creating an ETDefinition node at the appropriate place or
 * else just replacing terms.
 */
object insertDefinition {
  def apply( et: ExpansionTree, defn: Definition, replacementContext: Abs ): ExpansionTree = {
    val Abs( v, expr ) = replacementContext

    def definitionApplied = BetaReduction.betaNormalize( App( replacementContext, defn.what ) ).asInstanceOf[HOLFormula]

    ( et, expr ) match {
      case ( _, Apps( `v`, _ ) ) => // ctx = λ v. v […]
        ETDefinition( definitionApplied, et )

      case ( ETDefinition( _, child ), _ ) =>
        ETDefinition( definitionApplied, child )

      case ( ETNeg( s ), Neg( f ) ) =>
        ETNeg( insertDefinition( s, defn, Abs( v, f ) ) )

      case ( ETAnd( l, r ), And( f, g ) ) =>
        ETAnd( insertDefinition( l, defn, Abs( v, f ) ), insertDefinition( r, defn, Abs( v, g ) ) )

      case ( ETOr( l, r ), Or( f, g ) ) =>
        ETOr( insertDefinition( l, defn, Abs( v, f ) ), insertDefinition( r, defn, Abs( v, g ) ) )

      case ( ETImp( l, r ), Imp( f, g ) ) =>
        ETImp( insertDefinition( l, defn, Abs( v, f ) ), insertDefinition( r, defn, Abs( v, g ) ) )

      case ( ETStrongQuantifier( shallow, eigen, child ), Quant( _, _, _ ) ) =>
        val shallowNew = definitionApplied.asInstanceOf[HOLFormula]
        ETStrongQuantifier( shallowNew, eigen, insertDefinition( child, defn, instReplCtx( replacementContext, eigen ) ) )

      case ( ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ), Quant( x, f, _ ) ) =>
        throw new IllegalArgumentException( "Skolem nodes are not handled at this time." )

      case ( ETWeakQuantifier( shallow, instances ), Quant( _, _, _ ) ) =>
        val shallowNew = definitionApplied.asInstanceOf[HOLFormula]
        val instancesNew: Map[LambdaExpression, ExpansionTree] = ( for {
          ( t, e ) <- instances
          ctxNew = instReplCtx( replacementContext, t )
          treeNew = insertDefinition( e, defn, ctxNew )
        } yield ( t, treeNew ) ).toMap

        ETWeakQuantifier( shallowNew, instancesNew )

      case ( ETMerge( l, r ), _ ) =>
        ETMerge( insertDefinition( l, defn, replacementContext ), insertDefinition( r, defn, replacementContext ) )

      case ( ETWeakening( formula, pol ), _ ) =>
        ETWeakening( definitionApplied.asInstanceOf[HOLFormula], pol )

      case _ =>
        replaceWithContext( et, replacementContext, defn.what )
    }
  }
}

/**
 * Instantiates the quantifier inside a replacement context.
 *
 * Given λx ∀y P(x,y) and f(c), it will return λx P(x,f(c)).
 */
private[expansion] object instReplCtx {
  def apply( ctx: Abs, term: LambdaExpression ): Abs =
    ctx match {
      case Abs( x, quantFormula ) if freeVariables( term ) contains x =>
        val newX = rename( x, freeVariables( term ) )
        instReplCtx( Abs( newX, Substitution( x -> newX )( quantFormula ) ), term )
      case Abs( x, quantFormula: HOLFormula ) =>
        Abs( x, instantiate( quantFormula, term ) )
    }
}

object generalizeET {
  def apply( et: ExpansionTree, newShallow: HOLFormula ): ExpansionTree =
    HOLPosition.differingPositions( et.shallow, newShallow ).
      groupBy( pos => ( et.shallow( pos ), newShallow( pos ) ) ).
      foldLeft( et ) {
        case ( et_, ( ( what, by ), poss ) ) =>
          replaceWithContext( et_, replacementContext( what.exptype, et_.shallow, poss ), by )
      }
}

