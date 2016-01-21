package at.logic.gapt.proofs.expansion

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs.DagProof

trait ExpansionTree extends DagProof[ExpansionTree] {
  def shallow: HOLFormula
  def deep: HOLFormula
  def polarity: Boolean
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
}

case class ETAtom( atom: HOLAtom, polarity: Boolean ) extends ExpansionTree {
  def shallow = atom
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

case class ETWeakQuantifier( shallow: HOLFormula, instances: Map[LambdaExpression, ExpansionTree] ) extends ExpansionTree {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( true, x, t )
    case All( x, t ) => ( false, x, t )
  }

  for ( ( selectedTerm, child ) <- instances ) {
    require( child.polarity == polarity )
    require( child.shallow == BetaReduction.betaNormalize( Substitution( boundVar -> selectedTerm )( qfFormula ) ) )
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

case class ETStrongQuantifier( shallow: HOLFormula, eigenVariable: Var, child: ExpansionTree ) extends UnaryExpansionTree {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( false, x, t )
    case All( x, t ) => ( true, x, t )
  }

  require( child.polarity == polarity )
  require( child.shallow == Substitution( boundVar -> eigenVariable )( qfFormula ) )

  def deep = child.deep
}

case class ETSkolemQuantifier( shallow: HOLFormula, skolemTerm: LambdaExpression, child: ExpansionTree ) extends UnaryExpansionTree {
  val ( polarity, boundVar, qfFormula ) = shallow match {
    case Ex( x, t )  => ( false, x, t )
    case All( x, t ) => ( true, x, t )
  }

  require( child.polarity == polarity )
  require( child.shallow == Substitution( boundVar -> skolemTerm )( qfFormula ) )

  def deep = child.deep
}

object replaceET {
  def apply( et: ExpansionTree, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( replaceET( child1, repl ), replaceET( child2, repl ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = TermReplacement( formula, repl ) )
    case et @ ETAtom( atom, _ ) =>
      et.copy( atom = TermReplacement( atom, repl ) )

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
      ETStrongQuantifier( TermReplacement( shallow, repl ), TermReplacement( eigenVariable, repl ).asInstanceOf[Var], replaceET( child, repl ) )
    case ETSkolemQuantifier( shallow, eigenVariable, child ) =>
      ETSkolemQuantifier( TermReplacement( shallow, repl ), TermReplacement( eigenVariable, repl ), replaceET( child, repl ) )
  }
}

private[expansion] object expansionTreeSubstitution extends ClosedUnderSub[ExpansionTree] {
  def applySubstitution( subst: Substitution, et: ExpansionTree ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = subst( formula ) )
    case et @ ETAtom( atom, _ ) =>
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
        case skolemTerm    => ETSkolemQuantifier( subst( shallow ), skolemTerm, applySubstitution( subst, child ) )
      }
    case ETSkolemQuantifier( shallow, skolemTerm, child ) =>
      ETSkolemQuantifier( subst( shallow ), subst( skolemTerm ), applySubstitution( subst, child ) )
  }
}

object eigenVariablesET {
  def apply( tree: ExpansionTree ): Set[Var] = tree.subProofs collect { case ETStrongQuantifier( _, v, _ ) => v }
  def apply( s: ExpansionSequent ): Set[Var] = s.elements.flatMap { apply }.toSet
}

object replaceAtHOLPosition {
  def apply( et: ExpansionTree, pos: HOLPosition, exp: LambdaExpression ): ExpansionTree = {
    val rest = pos.tail
    ( et, pos.head ) match {
      case ( ETMerge( left, right ), _ )                => ETMerge( replaceAtHOLPosition( left, pos, exp ), replaceAtHOLPosition( right, pos, exp ) )

      case ( ETTop( _ ), _ ) | ( ETBottom( _ ), _ )     => et
      case ( ETAtom( formula, polarity ), _ )           => ETAtom( formula.replace( pos, exp ).asInstanceOf[HOLAtom], polarity )

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
      case ( ETSkolemQuantifier( formula, v, sub ), 1 ) => ETSkolemQuantifier( formula.replace( pos, exp ), v, replaceAtHOLPosition( sub, rest, exp ) )

      case ( ETWeakQuantifier( formula, instances ), 1 ) =>
        ETWeakQuantifier(
          formula.replace( pos, exp ),
          for ( ( term, instance ) <- instances )
            yield term -> replaceAtHOLPosition( instance, rest, exp )
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
    case ETSkolemQuantifier( sh, st, s ) => apply( s ) match {
      case ETWeakening( _, p ) => ETWeakening( sh, p )
      case r                   => ETSkolemQuantifier( sh, st, r )
    }
    case ETWeakQuantifier( sh, inst ) =>
      val cleanInst = inst mapValues apply filterNot { _._2.isInstanceOf[ETWeakening] }
      if ( cleanInst isEmpty ) ETWeakening( sh, t.polarity )
      else ETWeakQuantifier( sh, cleanInst )
    case _ => t
  }
}
