package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, instantiate }
import at.logic.gapt.proofs.Context

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

      case ( ETWeakening( _, _ ), _ )               => Set()
    }
}

object replaceAtHOLPosition {
  def apply( et: ExpansionTree, pos: HOLPosition, exp: Expr ): ExpansionTree =
    replaceWithContext( et, replacementContext( et.shallow( pos ).ty, et.shallow, Some( pos ) ), exp )
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
  def apply( et: ExpansionTree, replacementContext: Abs, exp: Expr )( implicit ctx: Context = Context() ): ExpansionTree = {
    def newFormula = BetaReduction.betaNormalize( App( replacementContext, exp ) ).asInstanceOf[Formula]
    def newAtom = newFormula.asInstanceOf[Atom]

    ( et, replacementContext ) match {
      case ( ETDefinition( sh, sub ), _ ) =>
        val Some( matching ) = syntacticMatching( replacementContext.term, et.shallow )
        val newCtx = commuteReplacementCtxWithDefEq( replacementContext, matching( replacementContext.variable ), sub.shallow )
        ETDefinition.ifNecessary( newFormula, apply( sub, newCtx, exp ) )

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

        val newSkArgs = skArgs.map( a => nameGen.fresh( Var( "x", a.ty ) ) )
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
            yield term -> apply( instance, instReplCtx( replacementContext, term ), exp ) )
      case _ => throw new IllegalArgumentException( s"Tree $et and context $replacementContext could not be handled." )
    }
  }
}

object commuteReplacementCtxWithDefEq {
  /**
   * Given c[x\t] =def a, tries to find c' such that c'[x\t] = a and c' =def c.
   *
   * Right now this only works if c[x\t] ~> a, and may fail even then.
   */
  def apply( x: Var, c: Expr, t: Expr, a: Expr )( implicit ctx: Context ): Expr =
    ( c, a ) match {
      case _ if Substitution( x -> t )( c ) == a => c
      case ( Apps( fn1, as1 ), Apps( fn2, as2 ) ) if fn1 == fn2 && !freeVariables( fn1 ).contains( x ) =>
        fn1( for ( ( a1, a2 ) <- as1 zip as2 ) yield apply( x, a1, t, a2 ) )
      case ( c @ Quant( y1, _, pol1 ), a @ Quant( y2, _, pol2 ) ) if y1.ty == y2.ty && pol1 == pol2 =>
        val y = rename( y1, freeVariables( c ) ++ freeVariables( a ) ++ freeVariables( t ) + x )
        Quant( y, apply( x, instantiate( c, y ), t, instantiate( a, y ) ).asInstanceOf[Formula], pol1 )
      case _ =>
        // imitate
        a match {
          case Apps( fn2 @ Const( _, _ ), as2 ) =>
            val pat = fn2( for ( ( a, i ) <- as2.zipWithIndex ) yield Var( s"x$i", a.ty ) )
            syntacticMatching( ctx.normalize( pat ), ctx.normalize( c ) ) match {
              case Some( subst ) =>
                return apply( x, subst( pat ), t, a )
              case _ =>
            }
          case _ =>
        }
        // reduce
        ctx.normalizer.reduce1( c ) match {
          case Some( c_ ) => apply( x, BetaReduction.betaNormalize( c_ ), t, a )
          case None =>
            throw new IllegalArgumentException( s"Cannot solve c'[$x\\$t] = $a\n  and c' =def $c" )
        }
    }

  def apply( replCtx: Abs, t: Expr, a: Expr )( implicit ctx: Context ): Abs =
    Abs( replCtx.variable, apply( replCtx.variable, replCtx.term, t, a ) )
}

/**
 * Inserts a definition into an expansion tree by either creating an ETDefinition node at the appropriate place or
 * else just replacing terms.
 */
object insertDefinition {
  def apply( et: ExpansionTree, defn: Definition, replacementContext: Abs ): ExpansionTree = {
    val Abs( v, expr ) = replacementContext

    def definitionApplied = BetaReduction.betaNormalize( App( replacementContext, defn.what ) ).asInstanceOf[Formula]

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
        val shallowNew = definitionApplied
        ETStrongQuantifier( shallowNew, eigen, insertDefinition( child, defn, instReplCtx( replacementContext, eigen ) ) )

      case ( ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ), Quant( x, f, _ ) ) =>
        throw new IllegalArgumentException( "Skolem nodes are not handled at this time." )

      case ( ETWeakQuantifier( shallow, instances ), Quant( _, _, _ ) ) =>
        val shallowNew = definitionApplied
        val instancesNew: Map[Expr, ExpansionTree] = ( for {
          ( t, e ) <- instances
          ctxNew = instReplCtx( replacementContext, t )
          treeNew = insertDefinition( e, defn, ctxNew )
        } yield ( t, treeNew ) ).toMap

        ETWeakQuantifier( shallowNew, instancesNew )

      case ( ETMerge( l, r ), _ ) =>
        ETMerge( insertDefinition( l, defn, replacementContext ), insertDefinition( r, defn, replacementContext ) )

      case ( ETWeakening( formula, pol ), _ ) =>
        ETWeakening( definitionApplied, pol )

      case _ =>
        replaceWithContext( et, replacementContext, defn.what )
    }
  }
}

object moveDefsUpward {
  private def apply( tree: ExpansionTree, expectedSh: Formula )( implicit ctx: Context ): ExpansionTree =
    ( tree, expectedSh ) match {
      case ( ETDefinition( _, t ), _ )                        => apply( t, expectedSh )
      case ( ETWeakening( _, pol ), _ )                       => ETWeakening( expectedSh, pol )
      case ( ETMerge( t1, t2 ), _ )                           => ETMerge( apply( t1, expectedSh ), apply( t2, expectedSh ) )
      case ( ETAtom( _, _ ) | ETTop( _ ) | ETBottom( _ ), _ ) => ETDefinition.ifNecessary( expectedSh, tree )
      case ( ETNeg( t ), Neg( f ) )                           => ETNeg( apply( t, f ) )
      case ( ETAnd( t1, t2 ), And( f1, f2 ) )                 => ETAnd( apply( t1, f1 ), apply( t2, f2 ) )
      case ( ETOr( t1, t2 ), Or( f1, f2 ) )                   => ETOr( apply( t1, f1 ), apply( t2, f2 ) )
      case ( ETImp( t1, t2 ), Imp( f1, f2 ) )                 => ETImp( apply( t1, f1 ), apply( t2, f2 ) )
      case ( ETStrongQuantifier( _, eig, t ), Quant( _, _, _ ) ) =>
        ETStrongQuantifier( expectedSh, eig, apply( t, instantiate( expectedSh, eig ) ) )
      case ( ETSkolemQuantifier( _, _, _, _ ), Quant( _, _, _ ) ) =>
        ETDefinition.ifNecessary( expectedSh, tree ) // TODO
      case ( ETWeakQuantifier( _, insts ), Quant( _, _, _ ) ) =>
        ETWeakQuantifier(
          expectedSh,
          for ( ( term, ch ) <- insts )
            yield term -> apply( ch, BetaReduction.betaNormalize( instantiate( expectedSh, term ) ) ) )
      case ( _, _ ) =>
        val expectedShWhnf = ctx.normalizer.whnf( expectedSh ).asInstanceOf[Formula]
        if ( expectedShWhnf == expectedSh ) {
          // We encountered a definition rule that was not valid in this context.
          ETDefinition( expectedSh, apply( tree, tree.shallow ) )
        } else {
          ETDefinition( expectedSh, apply( tree, expectedShWhnf ) )
        }
    }

  def apply( et: ExpansionTree )( implicit ctx: Context ): ExpansionTree = apply( et, et.shallow )
  def apply( es: ExpansionSequent )( implicit ctx: Context ): ExpansionSequent = es.map( apply )
  def apply( ep: ExpansionProof )( implicit ctx: Context ): ExpansionProof = ExpansionProof( apply( ep.expansionSequent ) )
}

/**
 * Instantiates the quantifier inside a replacement context.
 *
 * Given λx ∀y P(x,y) and f(c), it will return λx P(x,f(c)).
 */
object instReplCtx {
  def apply( ctx: Abs, term: Expr ): Abs =
    ctx match {
      case Abs( x, quantFormula ) if freeVariables( term ) contains x =>
        val newX = rename( x, freeVariables( term ) )
        instReplCtx( Abs( newX, Substitution( x -> newX )( quantFormula ) ), term )
      case Abs( x, quantFormula: Formula ) =>
        Abs( x, instantiate( quantFormula, term ) )
    }
}

object generalizeET {
  def apply( et: ExpansionTree, newShallow: Formula )( implicit ctx: Context ): ExpansionTree =
    HOLPosition.differingPositions( et.shallow, newShallow ).
      groupBy( pos => ( et.shallow( pos ), newShallow( pos ) ) ).
      foldLeft( et ) {
        case ( et_, ( ( what, by ), poss ) ) =>
          replaceWithContext( et_, replacementContext( what.ty, et_.shallow, poss ), by )
      }
}

