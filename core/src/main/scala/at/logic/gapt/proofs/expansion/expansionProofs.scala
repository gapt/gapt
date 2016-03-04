package at.logic.gapt.proofs.expansion

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.expr.hol.HOLPosition

import scala.collection.mutable

object linearizeStrictPartialOrder {
  def apply[T]( set: Iterable[T], relation: Iterable[( T, T )] ): Either[Seq[T], Seq[T]] =
    build( set.toSet, relation.toSet, Seq() )

  private def build[T]( set: Set[T], relation: Set[( T, T )], prefix: Seq[T] ): Either[Seq[T], Seq[T]] =
    if ( set isEmpty ) {
      Right( prefix )
    } else {
      set find { n => relation forall { _._2 != n } } match {
        case Some( next ) =>
          build( set - next, relation filterNot { _._1 == next }, prefix :+ next )
        case None =>
          val start = set.head
          val cycle = start +: walk( start, relation ).drop( 1 ).takeWhile( _ != start ) :+ start
          Left( cycle.toList )
      }
    }

  private def walk[T]( start: T, relation: Set[( T, T )] ): Stream[T] = {
    val Some( ( _, next ) ) = relation find { _._1 == start }
    next #:: walk( next, relation )
  }
}

case class ExpansionProof( expansionSequent: Sequent[ExpansionTree] ) {
  for ( ( tree, index ) <- expansionSequent.zipWithIndex ) require( tree.polarity == index.isSuc )

  {
    val evs = mutable.Set[Var]()
    val fvs = freeVariables( shallow )
    for {
      tree <- expansionSequent
      ETStrongQuantifier( _, ev, _ ) <- tree.treeLike.postOrder
    } {
      require( !evs.contains( ev ), s"duplicate eigenvariable $ev" )
      require( !fvs.contains( ev ), s"eigenvariable $ev is free in shallow sequent" )
      evs += ev
    }
  }

  def shallow = expansionSequent.shallow
  def deep = expansionSequent.deep

  val subProofs = expansionSequent.elements flatMap { _.subProofs } toSet
  val eigenVariables = for ( ETStrongQuantifier( _, ev, _ ) <- subProofs ) yield ev

  val dependencyRelation = for {
    ETWeakQuantifier( _, instances ) <- subProofs
    ( term, child ) <- instances
    ETStrongQuantifier( _, ev, _ ) <- child.subProofs
    evInTerm <- eigenVariables intersect freeVariables( term )
  } yield evInTerm -> ev
  val Right( linearizedDependencyRelation ) = linearizeStrictPartialOrder( eigenVariables, dependencyRelation )

  override def toString = expansionSequent.toString
}

case class ExpansionProofWithCut( expansionWithCutAxiom: ExpansionProof ) {
  import ExpansionProofWithCut._
  def expansionSequent = expansionWithCutAxiom.expansionSequent filter { _.shallow != cutAxiom }
  def eigenVariables = expansionWithCutAxiom.eigenVariables
  def deep = expansionWithCutAxiom.deep
  def shallow = expansionSequent map { _.shallow }
  def subProofs = expansionWithCutAxiom.subProofs

  val cuts = for {
    cutAxiomExpansion <- expansionWithCutAxiom.expansionSequent.antecedent
    if cutAxiomExpansion.shallow == cutAxiom
    cut <- expansionWithCutAxiom.expansionSequent( Ant( 0 ) )( HOLPosition( 1 ) )
    cut1 <- cut( HOLPosition( 1 ) )
    cut2 <- cut( HOLPosition( 2 ) )
  } yield ETImp( cut1, cut2 )

  def toExpansionProof = {
    require( cuts.isEmpty )
    ExpansionProof( expansionSequent )
  }

  override def toString = expansionWithCutAxiom.toString
}
object ExpansionProofWithCut {
  val cutAxiom = hof"∀X (X ⊃ X)"
  def apply( expansionSequentWithCutAxiom: ExpansionSequent ): ExpansionProofWithCut =
    ExpansionProofWithCut( ExpansionProof( expansionSequentWithCutAxiom ) )
  def apply( cuts: Seq[ETImp], expansionSequent: Sequent[ExpansionTree] ): ExpansionProofWithCut =
    apply(
      ETWeakQuantifier.withMerge(
        ExpansionProofWithCut.cutAxiom,
        for ( cut @ ETImp( cut1, cut2 ) <- cuts ) yield cut1.shallow -> cut
      ) +: expansionSequent
    )
}

private[expansion] object expansionProofSubstitution extends ClosedUnderSub[ExpansionProof] {
  override def applySubstitution( subst: Substitution, expansionProof: ExpansionProof ): ExpansionProof =
    if ( subst.domain intersect expansionProof.eigenVariables nonEmpty ) {
      applySubstitution( Substitution( subst.map -- expansionProof.eigenVariables ), expansionProof )
    } else {
      val substWithRenaming = subst compose Substitution(
        rename( expansionProof.eigenVariables intersect subst.range, expansionProof.eigenVariables union subst.range )
      )
      ExpansionProof( substWithRenaming( expansionProof.expansionSequent ) )
    }
}
private[expansion] object expansionProofWithCutSubstitution extends ClosedUnderSub[ExpansionProofWithCut] {
  override def applySubstitution( subst: Substitution, expansionProofWithCut: ExpansionProofWithCut ): ExpansionProofWithCut =
    ExpansionProofWithCut( subst( expansionProofWithCut.expansionWithCutAxiom ) )
}

object eliminateMerges {
  def apply( expansionProof: ExpansionProofWithCut ): ExpansionProofWithCut =
    new ExpansionProofWithCut( apply( expansionProof.expansionWithCutAxiom ) )

  def apply( expansionProof: ExpansionProof ): ExpansionProof =
    elim( expansionProof.expansionSequent )

  private def elim( expansionSequent: Sequent[ExpansionTree] ): ExpansionProof = {
    var needToMergeAgain = false
    var eigenVarSubst = Substitution()

    def merge( tree: ExpansionTree ): ExpansionTree = tree match {
      case ETMerge( t, s )             => merge2( t, s )
      case ETAtom( atom, pol )         => ETAtom( atom, pol )
      case ETWeakening( formula, pol ) => ETWeakening( formula, pol )
      case _: ETTop | _: ETBottom      => tree
      case ETNeg( t )                  => ETNeg( merge( t ) )
      case ETAnd( t, s )               => ETAnd( merge( t ), merge( s ) )
      case ETOr( t, s )                => ETOr( merge( t ), merge( s ) )
      case ETImp( t, s )               => ETImp( merge( t ), merge( s ) )
      case ETWeakQuantifier( shallow, inst ) =>
        ETWeakQuantifier(
          shallow,
          for ( ( selectedTerm, child ) <- inst )
            yield selectedTerm -> merge( child )
        )
      case tree: ETStrongQuantifier => tree.copy( child = merge( tree.child ) )
      case tree: ETSkolemQuantifier => tree.copy( child = merge( tree.child ) )
    }
    def merge2( tree1: ExpansionTree, tree2: ExpansionTree ): ExpansionTree = ( tree1, tree2 ) match {
      case ( _: ETWeakening, s ) => merge( s )
      case ( t, _: ETWeakening ) => merge( t )
      case ( ETMerge( t1, t2 ), s ) =>
        merge2( t1, t2 ) match {
          case t: ETMerge => ETMerge( t, merge( s ) )
          case t          => merge2( t, s )
        }
      case ( t, s: ETMerge )                    => merge2( s, t )
      case ( t: ETAtom, _: ETAtom )             => merge( t )
      case ( ETNeg( t ), ETNeg( s ) )           => ETNeg( merge2( t, s ) )
      case ( ETAnd( t1, t2 ), ETAnd( s1, s2 ) ) => ETAnd( merge2( t1, s1 ), merge2( t2, s2 ) )
      case ( ETOr( t1, t2 ), ETOr( s1, s2 ) )   => ETOr( merge2( t1, s1 ), merge2( t2, s2 ) )
      case ( ETImp( t1, t2 ), ETImp( s1, s2 ) ) => ETImp( merge2( t1, s1 ), merge2( t2, s2 ) )
      case ( ETWeakQuantifier( shallow, inst1 ), ETWeakQuantifier( _, inst2 ) ) =>
        ETWeakQuantifier(
          shallow,
          ( for ( selected <- inst1.keySet union inst2.keySet ) yield selected ->
          ( if ( !inst2.contains( selected ) ) merge( inst1( selected ) )
          else if ( !inst1.contains( selected ) ) merge( inst2( selected ) )
          else merge2( inst1( selected ), inst2( selected ) ) ) ).toMap
        )
      case ( tree1 @ ETStrongQuantifier( shallow, v1, t1 ), tree2 @ ETStrongQuantifier( _, v2, t2 ) ) =>
        if ( v1 == v2 ) {
          ETStrongQuantifier( shallow, v1, merge2( t1, t2 ) )
        } else {
          eigenVarSubst = eigenVarSubst compose Substitution( v2 -> v1 )
          needToMergeAgain = true

          ETMerge( merge( tree1 ), merge( tree2 ) )
        }
      case ( ETStrongQuantifier( _, v1, t1 ), ETSkolemQuantifier( shallow, st2, t2 ) ) =>
        needToMergeAgain = true
        if ( !eigenVarSubst.map.isDefinedAt( v1 ) )
          eigenVarSubst = eigenVarSubst compose Substitution( v1 -> st2 )

        ETMerge( merge( tree1 ), merge( tree2 ) )
      case ( t: ETSkolemQuantifier, s: ETStrongQuantifier ) => merge2( s, t )
      case ( ETSkolemQuantifier( shallow, st1, t1 ), ETSkolemQuantifier( _, st2, t2 ) ) =>
        if ( st1 == st2 ) {
          ETSkolemQuantifier( shallow, st1, merge2( t1, t2 ) )
        } else {
          ETMerge( merge( tree1 ), merge( tree2 ) )
        }
    }

    val mergedSequent = expansionSequent map merge

    if ( !needToMergeAgain ) {
      ExpansionProof( mergedSequent )
    } else {
      elim( mergedSequent map { eigenVarSubst( _ ) } )
    }
  }
}

object eliminateCutsET {
  def apply( expansionProof: ExpansionProofWithCut ): ExpansionProof = expansionProof.cuts match {
    case ETImp( cut1, cut2 ) +: rest => apply( singleStep( cut1, cut2, rest, expansionProof.expansionSequent ) )
    case Seq()                       => ExpansionProof( expansionProof.expansionSequent )
  }

  private def singleStep( cut1: ExpansionTree, cut2: ExpansionTree, rest: Seq[ETImp],
                          expansionSequent: Sequent[ExpansionTree] ): ExpansionProofWithCut = {
    def addCuts( extraCuts: ETImp* ) = ExpansionProofWithCut( extraCuts ++ rest, expansionSequent )

    def quantifiedCut(
      instances:     Map[LambdaExpression, ExpansionTree],
      eigenVariable: Var, child: ExpansionTree
    ): ExpansionProofWithCut = {
      if ( instances isEmpty ) return addCuts()

      val eigenVars = expansionSequent.elements.toSet + child ++ rest flatMap { eigenVariablesET( _ ) }

      val nameGen = rename.awayFrom( eigenVars union Set( eigenVariable )
        union instances.values.flatMap { eigenVariablesET( _ ) }.toSet )
      val renamings = for ( _ <- 0 until instances.size )
        yield Substitution( eigenVars map { ev => ev -> nameGen.fresh( ev ) } )
      val substs =
        for ( ( renaming, ( term, instance ) ) <- renamings zip instances.seq )
          yield renaming compose Substitution( eigenVariable -> term )

      eliminateMerges( ExpansionProofWithCut(
        ( for ( ( ( subst, renaming ), ( term, instance ) ) <- substs zip renamings zip instances.toSeq ) yield {
          if ( instance.polarity ) ETImp( renaming( instance ), subst( child ) )
          else ETImp( subst( child ), renaming( instance ) )
        } ) ++ ( for ( c <- rest; s <- substs ) yield s( c ).asInstanceOf[ETImp] ),
        for ( tree <- expansionSequent ) yield ETMerge( substs.map { _( tree ) } )
      ) )
    }

    ( cut1, cut2 ) match {
      case ( _: ETMerge, _ )                    => eliminateMerges( addCuts( ETImp( cut1, cut2 ) ) )
      case ( _, _: ETMerge )                    => eliminateMerges( addCuts( ETImp( cut1, cut2 ) ) )

      case ( _: ETWeakening, _ )                => addCuts()
      case ( _, _: ETWeakening )                => addCuts()
      case ( _: ETAtom, _: ETAtom )             => addCuts()
      case ( _: ETTop, _: ETTop )               => addCuts()
      case ( _: ETBottom, _: ETBottom )         => addCuts()
      case ( ETNeg( t1 ), ETNeg( t2 ) )         => addCuts( ETImp( t2, t1 ) )
      case ( ETAnd( t1, s1 ), ETAnd( t2, s2 ) ) => addCuts( ETImp( t1, t2 ), ETImp( s1, s2 ) )
      case ( ETOr( t1, s1 ), ETOr( t2, s2 ) )   => addCuts( ETImp( t1, t2 ), ETImp( s1, s2 ) )
      case ( ETImp( t1, s1 ), ETImp( t2, s2 ) ) => addCuts( ETImp( t2, t1 ), ETImp( s1, s2 ) )
      case ( ETWeakQuantifier( _, instances ), ETStrongQuantifier( _, eigenVariable, child ) ) =>
        quantifiedCut( instances, eigenVariable, child )
      case ( ETStrongQuantifier( _, eigenVariable, child ), ETWeakQuantifier( _, instances ) ) =>
        quantifiedCut( instances, eigenVariable, child )
    }

  }
}

object eliminateDefsET {
  object DefinitionFormula {
    def unapply( f: HOLFormula ) = f match {
      case All.Block( vs, And( Imp( Apps( d1: Const, vs1 ), r1 ),
        Imp( r2, Apps( d2, vs2 ) ) ) ) if d1 == d2 && r1 == r2 && vs == vs1 && vs == vs2 =>
        Some( ( vs, d1, r2 ) )
      case _ => None
    }
  }

  def apply( ep: ExpansionProof, pureFolWithoutEq: Boolean ): ExpansionProofWithCut =
    ep.shallow.find { case DefinitionFormula( _, _, _ ) => true case _ => false } match {
      case Some( idx ) => apply( apply( ep, idx, pureFolWithoutEq ), pureFolWithoutEq )
      case None        => ExpansionProofWithCut( ep )
    }
  def apply( ep: ExpansionProof, idx: SequentIndex, pureFolWithoutEq: Boolean ): ExpansionProof = {
    val ETWeakQuantifierBlock( DefinitionFormula( vs, definitionConst, definedFormula ), insts0 ) = ep.expansionSequent( idx )
    val negReplPos = HOLPosition( 1, 2 )
    val posReplPos = HOLPosition( 2, 1 )
    var insts = insts0 mapValues {
      case et =>
        ETMerge( et.shallow( posReplPos ).asInstanceOf[HOLFormula], true, getAtHOLPosition( et, posReplPos ) ) ->
          ETMerge( et.shallow( negReplPos ).asInstanceOf[HOLFormula], false, getAtHOLPosition( et, negReplPos ) )
    }

    val rest = ep.expansionSequent.delete( idx )
    val usesites = rest.elements.flatMap { _.subProofs }.
      collect { case ETDefinedAtom( Apps( d, args ), pol, _ ) => ( args, pol ) }.toSet
    insts = Map() ++
      usesites.map { _._1 }.map { as =>
        val ras = Substitution( vs zip as )( definedFormula )
        as -> ( ETWeakening( ras, true ), ETWeakening( ras, false ) )
      } ++
      insts

    if ( !pureFolWithoutEq ) {
      val newNegRepl = ETMerge( definedFormula, false, insts.values.map { _._2 }.map { generalizeET( _, definedFormula ) } )
      val newPosRepl = ETMerge( definedFormula, true, insts.values.map { _._1 }.map { generalizeET( _, definedFormula ) } )
      insts = insts map {
        case ( as, _ ) =>
          as -> ( Substitution( vs zip as )( newPosRepl ), Substitution( vs zip as )( newNegRepl ) )
      }
    }

    def replm: PartialFunction[LambdaExpression, LambdaExpression] = {
      case Apps( `definitionConst`, as ) => Substitution( vs zip as )( definedFormula )
    }
    def replf( f: HOLFormula ): HOLFormula = TermReplacement( f, replm )
    def repl( et: ExpansionTree ): ExpansionTree = et match {
      case ETMerge( a, b )                  => ETMerge( repl( a ), repl( b ) )
      case ETWeakening( sh, pol )           => ETWeakening( replf( sh ), pol )

      case ETTop( _ ) | ETBottom( _ )       => et
      case ETNeg( ch )                      => ETNeg( repl( ch ) )
      case ETAnd( l, r )                    => ETAnd( repl( l ), repl( r ) )
      case ETOr( l, r )                     => ETOr( repl( l ), repl( r ) )
      case ETImp( l, r )                    => ETImp( repl( l ), repl( r ) )
      case ETWeakQuantifier( sh, is )       => ETWeakQuantifier( replf( sh ), is mapValues repl )
      case ETStrongQuantifier( sh, ev, ch ) => ETStrongQuantifier( replf( sh ), ev, repl( ch ) )
      case ETSkolemQuantifier( sh, st, ch ) => ETSkolemQuantifier( replf( sh ), st, repl( ch ) )

      case ETDefinedAtom( Apps( `definitionConst`, as ), pol, _ ) =>
        if ( pol ) insts( as )._1 else insts( as )._2
      case ETAtom( Apps( f, _ ), _ ) if f != definitionConst => et
    }

    for ( ( _, ( pos, neg ) ) <- insts ) {
      require( !constants( pos.deep ).contains( definitionConst ) )
      require( !constants( neg.deep ).contains( definitionConst ) )
    }

    val newCuts = ETWeakQuantifier.withMerge(
      ExpansionProofWithCut.cutAxiom,
      insts.values.map { case ( pos, neg ) => pos.shallow -> ETImp( pos, neg ) }
    )

    val newES = ( newCuts +: ep.expansionSequent.delete( idx ).map { repl } ).
      groupBy { _.shallow }.map { _._2 }.map { ETMerge( _ ) }

    ExpansionProof( newES )
  }
}
