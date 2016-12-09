package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr.Polarity.{ Negative, Positive }
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, containsQuantifierOnLogicalLevel, instantiate }
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
  def shallow: HOLFormula

  /**
   * The formula represented by this tree, fully instantiated.
   */
  def deep: HOLFormula

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

  def apply( shallow: HOLFormula, polarity: Polarity, children: Iterable[ExpansionTree] ): ExpansionTree = {
    for ( ch <- children ) {
      require( ch.polarity == polarity )
      require( ch.shallow == shallow )
    }
    if ( children.nonEmpty ) apply( children ) else ETWeakening( shallow, polarity )
  }
}

/**
 * A tree representing a formula that originates from a weakening.
 * @param formula The represented formula.
 */
case class ETWeakening( formula: HOLFormula, polarity: Polarity ) extends ExpansionTree {
  def shallow = formula
  def deep = if ( polarity.inSuc ) Bottom() else Top()
  def immediateSubProofs = Seq()
}

/**
 * A tree representing an atomic formula.
 * @param atom The represented atom.
 */
case class ETAtom( atom: HOLAtom, polarity: Polarity ) extends ExpansionTree {
  def shallow = atom
  def deep = atom
  def immediateSubProofs = Seq()
}

/**
 * A tree whose deep formula is an atom, and whose shallow formula is the definitional expansion of the atom.
 *
 * This tree is used as an intermediate data structure during proof import from
 * clausal provers.  During clausification, it is often advantageous to abbreviate subformulas
 * by fresh atoms.  (This is necessary for polynomial-time clausification.)  These subformula abbreviations are
 * then translated into expansion trees using defined atoms and extra axioms.  If we replace a subformula φ(x,y) by
 * the atom D(x,y), then we have an ETDefinedAtom(D(x,y), ..., λxλy φ(x,y)) as an expansion of the subformula, as well
 * as expansions of the extra axiom ∀x∀y(D(x,y) <-> φ(x,y)).
 *
 * Another way to view defined atoms is the extracted expansions of non-atomic logical axioms in LK.  Consider a proof
 * in LK of φ:-φ that consists of just LogicalAxiom(φ).  Instead of first performing an atomic expansion, we could
 * directly extract an expansion proof with defined atoms:  ETDefinedAtom(D, InAnt, φ) :- ETDefinedAtom(D, InSuc, φ)
 * This expansion proof has the deep sequent D:-D and the shallow sequent φ:-φ.  (NB: this extraction is not implemented.)
 *
 * @param atom The atom (whose predicate symbol is defined)
 * @param polarity Polarity of the atom.
 * @param definedExpr Definitional expansion of the predicate symbol.
 */
case class ETDefinedAtom( atom: HOLAtom, polarity: Polarity, definedExpr: LambdaExpression ) extends ExpansionTree {
  val Apps( definitionConst: Const, arguments ) = atom
  require( freeVariables( definedExpr ).isEmpty )

  val shallow = BetaReduction.betaNormalize( definedExpr( arguments: _* ) ).asInstanceOf[HOLFormula]
  def deep = atom
  def immediateSubProofs = Seq()

  val definition = Definition( definitionConst, definedExpr )
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

/**
 * A general trait for trees representing quantified formulas.
 */
trait ETQuantifier extends ExpansionTree {
  def instances: Traversable[( LambdaExpression, ExpansionTree )]
}

object ETQuantifier {
  def unapply( et: ETQuantifier ): Some[( HOLFormula, Traversable[( LambdaExpression, ExpansionTree )] )] =
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

/**
 * Creates or matches a block of weak quantifiers.
 */
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
 * @param child An expansion tree of definedExpr(x,,1,,,...,x,,n,,).
 */
case class ETDefinition( shallow: HOLAtom, definedExpr: LambdaExpression, child: ExpansionTree ) extends UnaryExpansionTree {
  val HOLAtom( pred: Const, args ) = shallow
  require( pred.exptype == definedExpr.exptype )
  require( child.shallow == BetaReduction.betaNormalize( App( definedExpr, args ) ), s"child.shallow = ${child.shallow}; App(rhs, args) = ${App( definedExpr, args )}" )

  val polarity = child.polarity
  def deep = child.deep

  val definition = Definition( pred, definedExpr )
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

/**
 * Returns the eigenvariables in an expansion tree or expansion sequent.
 */
object eigenVariablesET {
  def apply( tree: ExpansionTree ): Set[Var] = tree.subProofs collect { case ETStrongQuantifier( _, v, _ ) => v }
  def apply( s: ExpansionSequent ): Set[Var] = s.elements.flatMap { apply }.toSet
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

