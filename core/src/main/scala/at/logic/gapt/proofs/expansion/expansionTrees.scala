package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, instantiate }
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.proofs._

import scala.collection.mutable

/**
 * A tree collecting instances of a formula. See, e.g., M. Baaz, S. Hetzl,
 * D. Weller: On the complexity of proof deskolemization, Journal of Symbolic
 * Logic, 77(2), 2012 for a formulation close to the one implemented here.
 */
trait ExpansionTree extends DagProof[ExpansionTree] {
  /**
   * The formula represented by this tree.
   */
  def shallow: Formula

  /**
   * The formula represented by this tree, fully instantiated.
   */
  def deep: Formula

  def polarity: Polarity

  def apply( pos: HOLPosition ): Set[ExpansionTree] = getAtHOLPosition( this, pos )

  def toSigRelativeString( implicit sig: BabelSignature ) =
    new ExpansionTreePrettyPrinter( sig ).export( this )
  override def toString = toSigRelativeString
}

/**
 * An expansion tree with one subtree.
 */
trait UnaryExpansionTree extends ExpansionTree {
  def child: ExpansionTree
  def immediateSubProofs = Seq( child )
}

/**
 * An expansion tree with two subtrees.
 */
trait BinaryExpansionTree extends ExpansionTree {
  def child1: ExpansionTree
  def child2: ExpansionTree
  def immediateSubProofs = Seq( child1, child2 )
}

/**
 * A node signifying that two trees need to be merged.
 *
 * The two trees must have the same shallow formula.
 * @param child1 The left subtree.
 * @param child2 The right subtree.
 */
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

  def apply( shallow: Formula, polarity: Polarity, children: Iterable[ExpansionTree] ): ExpansionTree = {
    for ( ch <- children ) {
      require( ch.polarity == polarity )
      require( ch.shallow == shallow )
    }
    if ( children.nonEmpty ) apply( children ) else ETWeakening( shallow, polarity )
  }

  def byShallowFormula( trees: Iterable[ExpansionTree] ): Vector[ExpansionTree] =
    trees.groupBy( t => t.shallow -> t.polarity ).valuesIterator.map( ETMerge( _ ) ).toVector

  def apply( expansionSequent: ExpansionSequent ): ExpansionSequent =
    Sequent( byShallowFormula( expansionSequent.antecedent ), byShallowFormula( expansionSequent.succedent ) )

  def apply( expansionProof: ExpansionProof ): ExpansionProof =
    ExpansionProof( apply( expansionProof.expansionSequent ) )
}
object ETMerges {
  def unapply( tree: ExpansionTree ): Some[Vector[ExpansionTree]] =
    tree match {
      case ETMerge( ETMerges( t ), ETMerges( s ) ) => Some( t ++ s )
      case _                                       => Some( Vector( tree ) )
    }
}

/**
 * A tree representing a formula that originates from a weakening.
 * @param formula The represented formula.
 */
case class ETWeakening( formula: Formula, polarity: Polarity ) extends ExpansionTree {
  def shallow = formula
  def deep = if ( polarity.inSuc ) Bottom() else Top()
  def immediateSubProofs = Seq()
}

/**
 * A tree representing an atomic formula.
 * @param atom The represented atom.
 */
case class ETAtom( atom: Atom, polarity: Polarity ) extends ExpansionTree {
  def shallow = atom
  def deep = atom
  def immediateSubProofs = Seq()
}

/**
 * A tree representing ⊤.
 */
case class ETTop( polarity: Polarity ) extends ExpansionTree {
  val shallow = Top()
  def deep = Top()
  def immediateSubProofs = Seq()
}

/**
 * A tree representing ⊥.
 */
case class ETBottom( polarity: Polarity ) extends ExpansionTree {
  val shallow = Bottom()
  def deep = Bottom()
  def immediateSubProofs = Seq()
}

/**
 * A tree representing ¬A.
 * @param child A tree representing A.
 */
case class ETNeg( child: ExpansionTree ) extends UnaryExpansionTree {
  val polarity = !child.polarity
  val shallow = -child.shallow
  def deep = -child.deep
}

/**
 * A tree representing A ∧ B.
 * @param child1 A tree representing A.
 * @param child2 A tree representing B.
 */
case class ETAnd( child1: ExpansionTree, child2: ExpansionTree ) extends BinaryExpansionTree {
  require( child1.polarity == child2.polarity )
  val polarity = child1.polarity
  val shallow = child1.shallow & child2.shallow
  def deep = child1.deep & child2.deep
}

/**
 * A tree representing A ∨ B.
 * @param child1 A tree representing A.
 * @param child2 A tree representing B.
 */
case class ETOr( child1: ExpansionTree, child2: ExpansionTree ) extends BinaryExpansionTree {
  require( child1.polarity == child2.polarity )
  val polarity = child1.polarity
  val shallow = child1.shallow | child2.shallow
  def deep = child1.deep | child2.deep
}

/**
 * A tree representing A ⊃ B.
 * @param child1 A tree representing A.
 * @param child2 A tree representing B.
 */
case class ETImp( child1: ExpansionTree, child2: ExpansionTree ) extends BinaryExpansionTree {
  require( child1.polarity != child2.polarity )
  val polarity = child2.polarity
  val shallow = child1.shallow --> child2.shallow
  def deep = child1.deep --> child2.deep
}

object ETCut {
  val cutAxiom = hof"∀X (X ⊃ X)"
  def apply( child1: ExpansionTree, child2: ExpansionTree ): ExpansionTree =
    ETWeakQuantifier.withMerge( cutAxiom, List( child1.shallow -> ETImp( child1, child2 ) ) )
  def apply( cuts: Seq[ETImp] ): ExpansionTree =
    ETWeakQuantifier.withMerge( cutAxiom, for ( cut <- cuts ) yield cut.child1.shallow -> cut )
  def apply( cuts: Seq[( ExpansionTree, ExpansionTree )] )( implicit dummyImplicit: DummyImplicit ): ExpansionTree =
    ETWeakQuantifier.withMerge( cutAxiom, for ( ( cut1, cut2 ) <- cuts ) yield cut1.shallow -> ETImp( cut1, cut2 ) )

  def isCutExpansion( tree: ExpansionTree ): Boolean =
    tree.polarity.inAnt && tree.shallow == cutAxiom

  def unapply( et: ExpansionTree ): Option[Set[ETImp]] =
    if ( isCutExpansion( et ) )
      Some {
        for {
          cut <- et( HOLPosition( 1 ) )
          cut1 <- cut( HOLPosition( 1 ) )
          cut2 <- cut( HOLPosition( 2 ) )
        } yield ETImp( cut1, cut2 )
      }
    else None
}

/**
 * A general trait for trees representing quantified formulas.
 */
trait ETQuantifier extends ExpansionTree {
  def instances: Traversable[( Expr, ExpansionTree )]
}

object ETQuantifier {
  def unapply( et: ETQuantifier ): Some[( Formula, Traversable[( Expr, ExpansionTree )] )] =
    Some( et.shallow -> et.instances )
}

/**
 * A tree representing a formula beginning with a weak quantifier, i.e., a positive existential or negative universal.
 *
 * It has the form Qx.A +^t,,1,,^ E,,1,, + … +^t,,n,,^ E,,n,,, where t,,1,,,…,t,,n,, are lambda terms of the same type
 * as x and E,,i,, is an expansion tree of A[x\t,,i,,].
 *
 * Its deep formula is E,,1,,.deep ∨ … ∨ E,,n,,.deep (in the case of an existential) or E,,1,,.deep ∧ … ∧ E,,n,,.deep
 * (in the case of a universal).
 * @param shallow The formula Qx.A.
 * @param instances A map containing the pairs t,,1,, → E,,1,,,…,t,,n,, → E,,n,,.
 */
case class ETWeakQuantifier( shallow: Formula, instances: Map[Expr, ExpansionTree] ) extends ETQuantifier {
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
  def withMerge( shallow: Formula, instances: Iterable[( Expr, ExpansionTree )] ): ExpansionTree = {
    ETWeakQuantifier( shallow, Map() ++ instances.groupBy( _._1 ).mapValues( children => ETMerge( children.map { _._2 } ) ) )
  }
}

/**
 * Creates or matches a block of weak quantifiers.
 */
object ETWeakQuantifierBlock {
  def apply( shallow: Formula, blockSize: Int, instances: Iterable[( Seq[Expr], ExpansionTree )] ): ExpansionTree =
    if ( blockSize == 0 ) {
      ETMerge( instances map { _._2 } )
    } else {
      ETWeakQuantifier( shallow, Map() ++ instances.groupBy( _._1.head ).mapValues { children =>
        apply( instantiate( shallow, children.head._1.head ), blockSize - 1,
          children map { case ( ts, et ) => ts.tail -> et } )
      } )
    }

  def unapply( et: ExpansionTree ): Some[( Formula, Int, Map[Seq[Expr], ExpansionTree] )] = {
    val instances = mutable.Map[Seq[Expr], Set[ExpansionTree]]().withDefaultValue( Set() )

    def walk( et: ExpansionTree, terms: Seq[Expr], n: Int ): Unit =
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

/**
 * A tree representing a formula beginning with a strong quantifier, i.e., a positive universal or a negative existential.
 *
 * It has the form Qx.A +^α^ E, where α is a variable (called the eigenvariable) and E is an expansion tree of A[x\α].
 *
 * Its deep formula is the deep formula of E.
 * @param shallow The formula A.
 * @param eigenVariable The variable α.
 * @param child The subtree E.
 */
case class ETStrongQuantifier( shallow: Formula, eigenVariable: Var, child: ExpansionTree ) extends ETQuantifier with UnaryExpansionTree {
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
  def apply( shallow: Formula, eigenVariables: Seq[Var], child: ExpansionTree ): ExpansionTree = eigenVariables match {
    case ev +: evs =>
      ETStrongQuantifier( shallow, ev,
        ETStrongQuantifierBlock( instantiate( shallow, ev ), evs, child ) )
    case Seq() => child
  }

  def unapply( et: ExpansionTree ): Some[( Formula, Seq[Var], ExpansionTree )] = et match {
    case ETStrongQuantifier( sh, ev, ETStrongQuantifierBlock( _, evs, child ) ) => Some( ( sh, ev +: evs, child ) )
    case _ => Some( ( et.shallow, Seq(), et ) )
  }
}

/**
 * A tree representing a formula beginning with a strong quantifier, i.e., a positive universal or a negative existential.
 *
 * As an example let us consider an expansion proof of ∀z P(c,z) :- ∃x ∀y P(x,y).
 * For Skolemization we introduce the Skolem function `s_1` (for the single strong quantifier), this function
 * has the Skolem definition `λx ∀y P(x,y)` (see [[at.logic.gapt.expr.hol.SkolemFunctions]] for details).
 * The natural expansion proof has the deep formula `P(c,s_1(c)) :- P(c,s_1(c))`, so we need a Skolem node with the
 * shallow formula `∀y P(c,y)`, and deep formula `P(c,s_1(c))`.  This Skolem node is constructed as
 * `ETSkolemQuantifier(∀y P(c,y), s_1(c), λx ∀y P(x,y), ETAtom(P(c,s_1(c)), InSuc))`.
 *
 * @param shallow  Shallow formula of the expansion tree.
 * @param skolemTerm  Skolem term that instantiates the strong quantifier, e.g. s_3(c)
 * @param skolemDef  Skolem definition for the Skolem symbol, see [[at.logic.gapt.expr.hol.SkolemFunctions]]
 * @param child  Expansion tree of the instantiated formula.
 */
case class ETSkolemQuantifier(
    shallow:    Formula,
    skolemTerm: Expr,
    skolemDef:  Expr,
    child:      ExpansionTree ) extends ETQuantifier with UnaryExpansionTree {
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
 * @param child An expansion tree of ψ(x,,1,,,...,x,,n,,).
 */
case class ETDefinition( shallow: Formula, child: ExpansionTree ) extends UnaryExpansionTree {
  val polarity = child.polarity
  def deep = child.deep
}

object ETDefinition {
  def ifNecessary( shallow: Formula, child: ExpansionTree ): ExpansionTree =
    if ( child.shallow == shallow )
      child
    else
      ETDefinition( shallow, child )
}

private[expansion] object replaceET {
  def apply( ep: ExpansionProof, repl: PartialFunction[Expr, Expr] ): ExpansionProof =
    ExpansionProof( ep.expansionSequent map { replaceET( _, repl ) } )

  def apply( et: ExpansionTree, repl: PartialFunction[Expr, Expr] ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( replaceET( child1, repl ), replaceET( child2, repl ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = TermReplacement( formula, repl ) )
    case et @ ETAtom( atom, _ ) =>
      et.copy( atom = TermReplacement( atom, repl ) )
    case ETDefinition( sh, child ) =>
      ETDefinition( TermReplacement( sh, repl ), replaceET( child, repl ) )

    case _: ETTop | _: ETBottom  => et
    case ETNeg( child )          => ETNeg( replaceET( child, repl ) )
    case ETAnd( child1, child2 ) => ETAnd( replaceET( child1, repl ), replaceET( child2, repl ) )
    case ETOr( child1, child2 )  => ETOr( replaceET( child1, repl ), replaceET( child2, repl ) )
    case ETImp( child1, child2 ) => ETImp( replaceET( child1, repl ), replaceET( child2, repl ) )

    case ETWeakQuantifier( shallow, instances ) =>
      ETWeakQuantifier.withMerge(
        TermReplacement( shallow, repl ),
        for ( ( selectedTerm, child ) <- instances.toSeq )
          yield TermReplacement( selectedTerm, repl ) -> replaceET( child, repl ) )

    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( eigenVariable, repl ).asInstanceOf[Var], replaceET( child, repl ) )
    case et @ ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      val Apps( _, newArgs ) = TermReplacement( et.skolemConst, repl )
      ETSkolemQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( skolemTerm, repl ),
        Abs( newArgs.map( _.asInstanceOf[Var] ), TermReplacement( skolemDef, repl ) ),
        replaceET( child, repl ) )
  }
}

private[expansion] object expansionTreeSubstitution extends ClosedUnderSub[ExpansionTree] {
  def applySubstitution( subst: Substitution, et: ExpansionTree ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = subst( formula ) )
    case et @ ETAtom( atom, _ ) =>
      et.copy( atom = subst( atom ).asInstanceOf[Atom] )
    case ETDefinition( sh, ch ) =>
      ETDefinition( subst( sh ), applySubstitution( subst, ch ) )

    case _: ETTop | _: ETBottom  => et
    case ETNeg( child )          => ETNeg( applySubstitution( subst, child ) )
    case ETAnd( child1, child2 ) => ETAnd( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )
    case ETOr( child1, child2 )  => ETOr( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )
    case ETImp( child1, child2 ) => ETImp( applySubstitution( subst, child1 ), applySubstitution( subst, child2 ) )

    case ETWeakQuantifier( shallow, instances ) =>
      ETWeakQuantifier.withMerge(
        subst( shallow ),
        for ( ( selectedTerm, child ) <- instances.toSeq )
          yield subst( selectedTerm ) -> applySubstitution( subst, child ) )

    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      subst( eigenVariable ) match {
        case eigenNew: Var => ETStrongQuantifier( subst( shallow ), eigenNew, applySubstitution( subst, child ) )
        case _             => throw new UnsupportedOperationException
      }
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      ETSkolemQuantifier( subst( shallow ), subst( skolemTerm ), skolemDef, applySubstitution( subst, child ) )
  }
}

/**
 * Returns the eigenvariables in an expansion tree or expansion sequent.
 */
object eigenVariablesET {
  def apply( tree: ExpansionTree ): Set[Var] = tree.subProofs collect { case ETStrongQuantifier( _, v, _ ) => v }
  def apply( s: ExpansionSequent ): Set[Var] = s.elements.flatMap { apply }.toSet
}

object isPropositionalET {
  def apply( tree: ExpansionTree ): Boolean =
    tree match {
      case ETWeakening( _, _ ) => true
      case ETMerge( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETAtom( _, _ ) | ETTop( _ ) | ETBottom( _ ) => true
      case ETNeg( sub ) => isPropositionalET( sub )
      case ETAnd( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETOr( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETImp( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETDefinition( _, sub ) => isPropositionalET( sub )
      case _ => false
    }
}

/**
 * Cleans up an expansion tree by introducing weakenings as late as possible.
 */
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

