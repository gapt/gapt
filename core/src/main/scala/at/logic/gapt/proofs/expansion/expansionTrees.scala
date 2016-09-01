package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr.Polarity.{ Negative, Positive }
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, SkolemFunctions, containsQuantifierOnLogicalLevel, instantiate }
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.proofs._

import scala.collection.mutable

trait ExpansionTree extends DagProof[ExpansionTree] {
  def shallow: HOLFormula
  def deep: HOLFormula
  def polarity: Polarity

  def apply( pos: HOLPosition ): Set[ExpansionTree] = getAtHOLPosition( this, pos )

  def toSigRelativeString( implicit sig: BabelSignature ) =
    new ExpansionTreePrettyPrinter( sig ).export( this )
  override def toString = toSigRelativeString
}

case class ETWeakening( formula: HOLFormula, polarity: Polarity ) extends ExpansionTree {
  def shallow = formula
  def deep = if ( polarity.inSuc ) Bottom() else Top()
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

  def deep = if ( polarity.positive ) child1.deep | child2.deep else child1.deep & child2.deep
}
object ETMerge {
  def apply( nonEmptyChildren: Iterable[ExpansionTree] ): ExpansionTree =
    nonEmptyChildren reduce { ETMerge( _, _ ) }

  def apply( shallow: HOLFormula, polarity: Polarity, children: Iterable[ExpansionTree] ): ExpansionTree = {
    for ( ch <- children ) {
      require( ch.polarity == polarity )
      require( ch.shallow == shallow )
    }
    if ( children.nonEmpty ) apply( children ) else ETWeakening( shallow, polarity )
  }
}

case class ETAtom( atom: HOLAtom, polarity: Polarity ) extends ExpansionTree {
  def shallow = atom
  def deep = atom
  def immediateSubProofs = Seq()
}

case class ETDefinedAtom( atom: HOLAtom, polarity: Polarity, definition: LambdaExpression ) extends ExpansionTree {
  val Apps( definitionConst: Const, arguments ) = atom
  require( freeVariables( definition ).isEmpty )

  val shallow = BetaReduction.betaNormalize( definition( arguments: _* ) ).asInstanceOf[HOLFormula]
  def deep = atom
  def immediateSubProofs = Seq()
}

case class ETTop( polarity: Polarity ) extends ExpansionTree {
  val shallow = Top()
  def deep = Top()
  def immediateSubProofs = Seq()
}

case class ETBottom( polarity: Polarity ) extends ExpansionTree {
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
    case Ex( x, t )  => ( Polarity.InSuccedent, x, t )
    case All( x, t ) => ( Polarity.InAntecedent, x, t )
  }

  for ( ( selectedTerm, child ) <- instances ) {
    require( child.polarity == polarity )
    val correctShallow = BetaReduction.betaNormalize( Substitution( boundVar -> selectedTerm )( qfFormula ) )
    require( child.shallow == correctShallow, s"Incorrect shallow formula:\n${child.shallow} !=\n $correctShallow" )
  }

  def deep =
    if ( polarity.inSuc ) Or( instances.values map { _.deep } )
    else And( instances.values map { _.deep } )

  def immediateSubProofs = instances.values.toSeq
  private lazy val product = Seq( shallow ) ++ instances.view.flatMap { case ( selectedTerm, child ) => Seq( selectedTerm, child ) }
  override def productArity = product.size
  override def productElement( n: Int ) = product( n )
}
object ETWeakQuantifier {
  def withMerge( shallow: HOLFormula, instances: Iterable[( LambdaExpression, ExpansionTree )] ): ExpansionTree = {
    ETWeakQuantifier( shallow, Map() ++ instances.groupBy( _._1 ).mapValues( children => ETMerge( children.map { _._2 } ) ) )
  }
}
object ETWeakQuantifierBlock {
  def apply( shallow: HOLFormula, blockSize: Int, instances: Iterable[( Seq[LambdaExpression], ExpansionTree )] ): ExpansionTree =
    if ( blockSize == 0 ) {
      ETMerge( instances map { _._2 } )
    } else {
      ETWeakQuantifier( shallow, Map() ++ instances.groupBy( _._1.head ).mapValues { children =>
        apply( instantiate( shallow, children.head._1.head ), blockSize - 1,
          children map { case ( ts, et ) => ts.tail -> et } )
      } )
    }

  def unapply( et: ExpansionTree ): Some[( HOLFormula, Int, Map[Seq[LambdaExpression], ExpansionTree] )] = {
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
      case ( Polarity.InSuccedent, Ex.Block( vs, _ ) )   => vs.size
      case ( Polarity.InAntecedent, All.Block( vs, _ ) ) => vs.size
    }

    walk( et, Seq(), numberQuants )

    Some( ( et.shallow, numberQuants, Map() ++ instances.mapValues( ETMerge( _ ) ) ) )
  }
}

case class ETStrongQuantifier( shallow: HOLFormula, eigenVariable: Var, child: ExpansionTree ) extends ETQuantifier with UnaryExpansionTree {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( Polarity.InAntecedent, x, t )
    case All( x, t ) => ( Polarity.InSuccedent, x, t )
  }

  require( child.polarity == polarity )
  require( child.shallow == Substitution( boundVar -> eigenVariable )( qfFormula ) )

  def instances = Some( eigenVariable -> child )

  def deep = child.deep
}
object ETStrongQuantifierBlock {
  def apply( shallow: HOLFormula, eigenVariables: Seq[Var], child: ExpansionTree ): ExpansionTree = eigenVariables match {
    case ev +: evs =>
      ETStrongQuantifier( shallow, ev,
        ETStrongQuantifierBlock( instantiate( shallow, ev ), evs, child ) )
    case Seq() => child
  }

  def unapply( et: ExpansionTree ): Some[( HOLFormula, Seq[Var], ExpansionTree )] = et match {
    case ETStrongQuantifier( sh, ev, ETStrongQuantifierBlock( _, evs, child ) ) => Some( ( sh, ev +: evs, child ) )
    case _ => Some( ( et.shallow, Seq(), et ) )
  }
}

case class ETSkolemQuantifier(
    shallow:    HOLFormula,
    skolemTerm: LambdaExpression,
    skolemDef:  LambdaExpression,
    child:      ExpansionTree
) extends ETQuantifier with UnaryExpansionTree {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( Polarity.InAntecedent, x, t )
    case All( x, t ) => ( Polarity.InSuccedent, x, t )
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
      val cleanInst = Map() ++ inst.mapValues( apply ).filterNot { _._2.isInstanceOf[ETWeakening] }
      if ( cleanInst isEmpty ) ETWeakening( sh, t.polarity )
      else ETWeakQuantifier( sh, cleanInst )
    case _ => t
  }
}

