package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, instantiate }
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.proofs.DagProof

import scala.collection.mutable

trait ExpansionTree extends DagProof[ExpansionTree] {
  def shallow: HOLFormula
  def deep: HOLFormula
  def polarity: Boolean

  def apply( pos: HOLPosition ): Set[ExpansionTree] = getAtHOLPosition( this, pos )

  def toSigRelativeString( implicit sig: BabelSignature ) =
    new ExpansionTreePrettyPrinter( sig ).export( this )
  override def toString = toSigRelativeString
}

case class ETWeakening( formula: HOLFormula, polarity: Boolean ) extends ExpansionTree {
  def shallow = formula
  def deep = if ( polarity ) Bottom() else Top()
  def immediateSubProofs = Seq()
}

trait UnaryExpansionTree extends ExpansionTree {
  def child: ExpansionTree
  def immediateSubProofs = Seq( child )
}

trait BinaryExpansionTree extends ExpansionTree {
  def child1: ExpansionTree
  def child2: ExpansionTree
  def immediateSubProofs = Seq( child1, child2 )
}

case class ETMerge( child1: ExpansionTree, child2: ExpansionTree ) extends BinaryExpansionTree {
  require( child1.polarity == child2.polarity )
  val polarity = child1.polarity

  require( child1.shallow == child2.shallow )
  val shallow = child1.shallow

  def deep = if ( polarity ) child1.deep | child2.deep else child1.deep & child2.deep
}
object ETMerge {
  def apply( nonEmptyChildren: Iterable[ExpansionTree] ): ExpansionTree =
    nonEmptyChildren reduce { ETMerge( _, _ ) }

  def apply( shallow: HOLFormula, polarity: Boolean, children: Iterable[ExpansionTree] ): ExpansionTree = {
    for ( ch <- children ) {
      require( ch.polarity == polarity )
      require( ch.shallow == shallow )
    }
    if ( children.nonEmpty ) apply( children ) else ETWeakening( shallow, polarity )
  }
}

case class ETAtom( atom: HOLAtom, polarity: Boolean ) extends ExpansionTree {
  def shallow = atom
  def deep = atom
  def immediateSubProofs = Seq()
}

case class ETDefinedAtom( atom: HOLAtom, polarity: Boolean, definition: LambdaExpression ) extends ExpansionTree {
  val Apps( definitionConst: Const, arguments ) = atom
  require( freeVariables( definition ).isEmpty )

  val shallow = BetaReduction.betaNormalize( definition( arguments: _* ) ).asInstanceOf[HOLFormula]
  def deep = atom
  def immediateSubProofs = Seq()
}

case class ETTop( polarity: Boolean ) extends ExpansionTree {
  val shallow = Top()
  def deep = Top()
  def immediateSubProofs = Seq()
}

case class ETBottom( polarity: Boolean ) extends ExpansionTree {
  val shallow = Bottom()
  def deep = Bottom()
  def immediateSubProofs = Seq()
}

case class ETNeg( child: ExpansionTree ) extends UnaryExpansionTree {
  val polarity = !child.polarity
  val shallow = -child.shallow
  def deep = -child.deep
}

case class ETAnd( child1: ExpansionTree, child2: ExpansionTree ) extends BinaryExpansionTree {
  require( child1.polarity == child2.polarity )
  val polarity = child1.polarity
  val shallow = child1.shallow & child2.shallow
  def deep = child1.deep & child2.deep
}

case class ETOr( child1: ExpansionTree, child2: ExpansionTree ) extends BinaryExpansionTree {
  require( child1.polarity == child2.polarity )
  val polarity = child1.polarity
  val shallow = child1.shallow | child2.shallow
  def deep = child1.deep | child2.deep
}

case class ETImp( child1: ExpansionTree, child2: ExpansionTree ) extends BinaryExpansionTree {
  require( child1.polarity != child2.polarity )
  val polarity = child2.polarity
  val shallow = child1.shallow --> child2.shallow
  def deep = child1.deep --> child2.deep
}

trait ETQuantifier extends ExpansionTree {
  def instances: Traversable[( LambdaExpression, ExpansionTree )]
}
object ETQuantifier {
  def unapply( et: ETQuantifier ): Some[( HOLFormula, Traversable[( LambdaExpression, ExpansionTree )] )] =
    Some( et.shallow -> et.instances )
}

case class ETWeakQuantifier( shallow: HOLFormula, instances: Map[LambdaExpression, ExpansionTree] ) extends ETQuantifier {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( true, x, t )
    case All( x, t ) => ( false, x, t )
  }

  for ( ( selectedTerm, child ) <- instances ) {
    require( child.polarity == polarity )
    val correctShallow = BetaReduction.betaNormalize( Substitution( boundVar -> selectedTerm )( qfFormula ) )
    require( child.shallow == correctShallow, s"Incorrect shallow formula:\n${child.shallow} !=\n $correctShallow" )
  }

  def deep =
    if ( polarity ) Or( instances.values map { _.deep } )
    else And( instances.values map { _.deep } )

  def immediateSubProofs = instances.values.toSeq
  private lazy val product = shallow +: instances.toSeq.flatMap { case ( selectedTerm, child ) => Seq( selectedTerm, child ) }
  override def productArity = product.size
  override def productElement( n: Int ) = product( n )
}
object ETWeakQuantifier {
  def withMerge( shallow: HOLFormula, instances: Iterable[( LambdaExpression, ExpansionTree )] ): ExpansionTree = {
    ETWeakQuantifier( shallow, instances groupBy { _._1 } mapValues { children => ETMerge( children map { _._2 } ) } )
  }
}
object ETWeakQuantifierBlock {
  def apply( shallow: HOLFormula, blockSize: Int, instances: Iterable[( Seq[LambdaExpression], ExpansionTree )] ): ExpansionTree =
    if ( blockSize == 0 ) {
      ETMerge( instances map { _._2 } )
    } else {
      ETWeakQuantifier( shallow, instances groupBy { _._1.head } mapValues { children =>
        apply( instantiate( shallow, children.head._1.head ), blockSize - 1,
          children map { case ( ts, et ) => ts.tail -> et } )
      } )
    }

  def unapply( et: ExpansionTree ): Some[( HOLFormula, Map[Seq[LambdaExpression], ExpansionTree] )] = {
    val instances = mutable.Map[Seq[LambdaExpression], Set[ExpansionTree]]().withDefaultValue( Set() )

    def walk( et: ExpansionTree, terms: Seq[LambdaExpression], n: Int ): Unit =
      if ( n == 0 ) instances( terms ) += et else et match {
        case ETWeakQuantifier( _, insts ) =>
          for ( ( term, child ) <- insts )
            walk( child, terms :+ term, n - 1 )
        case ETMerge( a, b ) =>
          walk( a, terms, n )
          walk( b, terms, n )
        case ETWeakening( _, _ ) =>
      }

    val numberQuants = ( et.polarity, et.shallow ) match {
      case ( true, Ex.Block( vs, _ ) )   => vs.size
      case ( false, All.Block( vs, _ ) ) => vs.size
    }

    walk( et, Seq(), numberQuants )

    Some( et.shallow -> instances.toMap.mapValues( ETMerge( _ ) ) )
  }
}

case class ETStrongQuantifier( shallow: HOLFormula, eigenVariable: Var, child: ExpansionTree ) extends ETQuantifier with UnaryExpansionTree {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( false, x, t )
    case All( x, t ) => ( true, x, t )
  }

  require( child.polarity == polarity )
  require( child.shallow == Substitution( boundVar -> eigenVariable )( qfFormula ) )

  def instances = Some( eigenVariable -> child )

  def deep = child.deep
}

case class ETSkolemQuantifier(
    shallow:    HOLFormula,
    skolemTerm: LambdaExpression,
    skolemDef:  LambdaExpression,
    child:      ExpansionTree
) extends ETQuantifier with UnaryExpansionTree {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( false, x, t )
    case All( x, t ) => ( true, x, t )
  }

  val Apps( skolemConst: Const, skolemArgs ) = skolemTerm
  require( BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) ) == shallow )

  require( child.polarity == polarity )
  require( child.shallow == Substitution( boundVar -> skolemTerm )( qfFormula ) )

  def instances = Some( skolemTerm -> child )

  def deep = child.deep
}

/**
 * Expansion tree node for definitions.
 *
 * @param shallow An atom P(x,,1,,,..., x,,n,,) where P stands for a more complex formula.
 * @param definedExpr The expression that P abbreviates. Must have the same type as P.
 * @param child An expansion tree with shallowFormula definedExpr(x,,1,,,...,x,,n,,)
 */
case class ETDefinition( shallow: HOLAtom, definedExpr: LambdaExpression, child: ExpansionTree ) extends UnaryExpansionTree {
  val HOLAtom( pred: Const, args ) = shallow
  require( pred.exptype == definedExpr.exptype )
  require( child.shallow == BetaReduction.betaNormalize( App( definedExpr, args ) ), s"child.shallow = ${child.shallow}; App(rhs, args) = ${App( definedExpr, args )}" )

  val polarity = child.polarity
  def deep = child.deep
}

private[expansion] object replaceET {
  def apply( ep: ExpansionProof, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionProof =
    ExpansionProof( ep.expansionSequent map { replaceET( _, repl ) } )

  def apply( et: ExpansionTree, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( replaceET( child1, repl ), replaceET( child2, repl ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = TermReplacement( formula, repl ) )
    case et @ ETAtom( atom, _ ) =>
      et.copy( atom = TermReplacement( atom, repl ) )
    case ETDefinedAtom( atom, pol, definition ) =>
      ETDefinedAtom( TermReplacement( atom, repl ), pol, TermReplacement( definition, repl ) )

    case _: ETTop | _: ETBottom  => et
    case ETNeg( child )          => ETNeg( replaceET( child, repl ) )
    case ETAnd( child1, child2 ) => ETAnd( replaceET( child1, repl ), replaceET( child2, repl ) )
    case ETOr( child1, child2 )  => ETOr( replaceET( child1, repl ), replaceET( child2, repl ) )
    case ETImp( child1, child2 ) => ETImp( replaceET( child1, repl ), replaceET( child2, repl ) )

    case ETWeakQuantifier( shallow, instances ) =>
      ETWeakQuantifier.withMerge(
        TermReplacement( shallow, repl ),
        for ( ( selectedTerm, child ) <- instances.toSeq )
          yield TermReplacement( selectedTerm, repl ) -> replaceET( child, repl )
      )

    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( eigenVariable, repl ).asInstanceOf[Var], replaceET( child, repl )
      )
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      ETSkolemQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( skolemTerm, repl ),
        TermReplacement( skolemDef, repl ),
        replaceET( child, repl )
      )
  }
}

private[expansion] object expansionTreeSubstitution extends ClosedUnderSub[ExpansionTree] {
  def applySubstitution( subst: Substitution, et: ExpansionTree ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = subst( formula ) )
    case et @ ETAtom( atom, _ ) =>
      et.copy( atom = subst( atom ).asInstanceOf[HOLAtom] )
    case et @ ETDefinedAtom( atom, _, _ ) =>
      et.copy( atom = subst( atom ).asInstanceOf[HOLAtom] )

    case _: ETTop | _: ETBottom  => et
    case ETNeg( child )          => ETNeg( applySubstitution( subst, child ) )
    case ETAnd( child1, child2 ) => ETAnd( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )
    case ETOr( child1, child2 )  => ETOr( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )
    case ETImp( child1, child2 ) => ETImp( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )

    case ETWeakQuantifier( shallow, instances ) =>
      ETWeakQuantifier.withMerge(
        subst( shallow ),
        for ( ( selectedTerm, child ) <- instances.toSeq )
          yield subst( selectedTerm ) -> applySubstitution( subst, child )
      )

    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      subst( eigenVariable ) match {
        case eigenNew: Var => ETStrongQuantifier( subst( shallow ), eigenNew, applySubstitution( subst, child ) )
        case _             => throw new UnsupportedOperationException
      }
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      ETSkolemQuantifier( subst( shallow ), subst( skolemTerm ), skolemDef, applySubstitution( subst, child ) )
  }
}

object eigenVariablesET {
  def apply( tree: ExpansionTree ): Set[Var] = tree.subProofs collect { case ETStrongQuantifier( _, v, _ ) => v }
  def apply( s: ExpansionSequent ): Set[Var] = s.elements.flatMap { apply }.toSet
}

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

object replaceAtLambdaPosition {
  def apply( et: ExpansionTree, pos: LambdaPosition, exp: LambdaExpression ): ExpansionTree = {
    val rest = pos.tail
    ( et, pos.head ) match {
      //FIXME: avoid the cast to HOLFormula
      case ( ETMerge( left, right ), _ )                => ETMerge( replaceAtLambdaPosition( left, pos, exp ), replaceAtLambdaPosition( right, pos, exp ) )

      case ( ETTop( _ ), _ ) | ( ETBottom( _ ), _ )     => et
      case ( ETAtom( formula, polarity ), _ )           => ETAtom( formula.replace( pos, exp ).asInstanceOf[HOLAtom], polarity )

      case ( ETWeakening( formula, polarity ), _ )      => ETWeakening( formula.replace( pos, exp ).asInstanceOf[HOLFormula], polarity )

      case ( ETNeg( sub ), 1 )                          => ETNeg( replaceAtLambdaPosition( sub, rest, exp ) )

      case ( ETAnd( left, right ), 1 )                  => ETAnd( replaceAtLambdaPosition( left, rest, exp ), right )
      case ( ETAnd( left, right ), 2 )                  => ETAnd( left, replaceAtLambdaPosition( right, rest, exp ) )

      case ( ETOr( left, right ), 1 )                   => ETOr( replaceAtLambdaPosition( left, rest, exp ), right )
      case ( ETOr( left, right ), 2 )                   => ETOr( left, replaceAtLambdaPosition( right, rest, exp ) )

      case ( ETImp( left, right ), 1 )                  => ETImp( replaceAtLambdaPosition( left, rest, exp ), right )
      case ( ETImp( left, right ), 2 )                  => ETImp( left, replaceAtLambdaPosition( right, rest, exp ) )

      //FIXME: Quantifier cases are not entirely safe: What if the eigenvariable or the instances are replaced?
      case ( ETStrongQuantifier( formula, v, sub ), 1 ) => ETStrongQuantifier( formula.replace( pos, exp ).asInstanceOf[HOLFormula], v, replaceAtLambdaPosition( sub, rest, exp ) )
      case ( ETSkolemQuantifier( formula, skt, skf, sub ), 1 ) =>
        ETSkolemQuantifier( formula.replace( pos, exp ).asInstanceOf[HOLFormula], skt, skf, replaceAtLambdaPosition( sub, rest, exp ) )

      case ( ETWeakQuantifier( formula, instances ), 1 ) =>
        ETWeakQuantifier(
          formula.replace( pos, exp ).asInstanceOf[HOLFormula],
          for ( ( term, instance ) <- instances )
            yield term -> replaceAtLambdaPosition( instance, rest, exp )
        )
    }
  }
}

object cleanStructureET {
  def apply( t: ExpansionTree ): ExpansionTree = t match {
    case ETNeg( s ) => apply( s ) match {
      case ETWeakening( f, p ) => ETWeakening( -f, !p )
      case r                   => ETNeg( r )
    }
    case ETAnd( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETWeakening( f1, p ), ETWeakening( f2, _ ) ) => ETWeakening( f1 & f2, p )
      case ( r1, r2 )                                     => ETAnd( r1, r2 )
    }
    case ETOr( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETWeakening( f1, p ), ETWeakening( f2, _ ) ) => ETWeakening( f1 | f2, p )
      case ( r1, r2 )                                     => ETOr( r1, r2 )
    }
    case ETImp( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETWeakening( f1, _ ), ETWeakening( f2, p ) ) => ETWeakening( f1 --> f2, p )
      case ( r1, r2 )                                     => ETImp( r1, r2 )
    }
    case ETStrongQuantifier( sh, ev, s ) => apply( s ) match {
      case ETWeakening( _, p ) => ETWeakening( sh, p )
      case r                   => ETStrongQuantifier( sh, ev, r )
    }
    case ETSkolemQuantifier( sh, st, sf, s ) => apply( s ) match {
      case ETWeakening( _, p ) => ETWeakening( sh, p )
      case r                   => ETSkolemQuantifier( sh, st, sf, r )
    }
    case ETWeakQuantifier( sh, inst ) =>
      val cleanInst = inst mapValues apply filterNot { _._2.isInstanceOf[ETWeakening] }
      if ( cleanInst isEmpty ) ETWeakening( sh, t.polarity )
      else ETWeakQuantifier( sh, cleanInst )
    case _ => t
  }
}
