package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk.{ solve, LKProof }
import at.logic.gapt.provers.escargot.Escargot

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

case class ExpansionProofWithCut( cuts: Seq[ETImp], expansionSequent: Sequent[ExpansionTree] ) {
  for ( ( tree, index ) <- expansionSequent.zipWithIndex ) require( tree.polarity == index.isSuc )
  for ( cut @ ETImp( cut1, cut2 ) <- cuts ) {
    require( !cut.polarity )
    require( cut1.shallow == cut2.shallow )
  }

  {
    val evs = mutable.Set[Var]()
    val fvs = freeVariables( shallow )
    for ( tree <- cuts ++: expansionSequent; ETStrongQuantifier( _, ev, _ ) <- tree.treeLike.postOrder ) {
      require( !evs.contains( ev ), s"duplicate eigenvariable $ev" )
      require( !fvs.contains( ev ), s"eigenvariable $ev is free in shallow sequent" )
      evs += ev
    }
  }

  def shallow = expansionSequent map { _.shallow }
  def deep = cuts.map { _.deep } ++: expansionSequent.map { _.deep }

  def subProofs = expansionSequent.elements.toSet ++ cuts flatMap { _.subProofs }
  val eigenVariables = for ( ETStrongQuantifier( _, ev, _ ) <- subProofs ) yield ev

  val dependencyRelation = for {
    ETWeakQuantifier( _, instances ) <- subProofs
    ( term, child ) <- instances
    ETStrongQuantifier( _, ev, _ ) <- child.subProofs
    evInTerm <- eigenVariables intersect freeVariables( term )
  } yield evInTerm -> ev
  val Right( linearizedDependencyRelation ) = linearizeStrictPartialOrder( eigenVariables, dependencyRelation )

  def toExpansionProof: ExpansionProof = {
    require( cuts isEmpty )
    ExpansionProof( expansionSequent )
  }
}

class ExpansionProof( expansionSequent: Sequent[ExpansionTree] ) extends ExpansionProofWithCut( Seq(), expansionSequent )
object ExpansionProof {
  def apply( expansionSequent: Sequent[ExpansionTree] ) = new ExpansionProof( expansionSequent )
  def unapply( expansionProof: ExpansionProof ) = Some( expansionProof.expansionSequent )
}

private[expansion] object expansionProofSubstitution extends ClosedUnderSub[ExpansionProofWithCut] {
  override def applySubstitution( subst: Substitution, expansionProof: ExpansionProofWithCut ): ExpansionProofWithCut =
    if ( subst.domain intersect expansionProof.eigenVariables nonEmpty ) {
      applySubstitution( Substitution( subst.map -- expansionProof.eigenVariables ), expansionProof )
    } else {
      val substWithRenaming = subst compose Substitution(
        rename( expansionProof.eigenVariables intersect subst.range, expansionProof.eigenVariables union subst.range )
      )
      ExpansionProofWithCut( substWithRenaming( expansionProof.cuts ) map { _.asInstanceOf[ETImp] }, substWithRenaming( expansionProof.expansionSequent ) )
    }
}

object eliminateMerges {
  def apply( expansionProof: ExpansionProofWithCut ): ExpansionProofWithCut =
    elim( expansionProof.cuts, expansionProof.expansionSequent )

  def apply( expansionProof: ExpansionProof ): ExpansionProof =
    apply( expansionProof: ExpansionProofWithCut ).toExpansionProof

  private def elim( cuts: Seq[ETImp], expansionSequent: Sequent[ExpansionTree] ): ExpansionProofWithCut = {
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
          ( if ( !inst2.contains( selected ) ) inst1( selected )
          else if ( !inst1.contains( selected ) ) inst2( selected )
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

    val mergedCuts = cuts.groupBy { _.shallow }.values.toList.map { ETMerge( _ ) }.map { merge }
    val mergedSequent = expansionSequent map merge

    if ( !needToMergeAgain ) {
      ExpansionProofWithCut( mergedCuts map { _.asInstanceOf[ETImp] }, mergedSequent )
    } else elim(
      mergedCuts map { eigenVarSubst( _ ) } map { _.asInstanceOf[ETImp] },
      mergedSequent map { eigenVarSubst( _ ) }
    )
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

      var renamings = Seq[Substitution]()
      for ( _ <- 0 until instances.size )
        renamings :+= Substitution( rename( eigenVars, eigenVars union renamings.flatMap { r => freeVariables( r.range ) }.toSet union instances.values.flatMap { eigenVariablesET( _ ) }.toSet ) )
      val substs =
        for ( ( renaming, ( term, instance ) ) <- renamings zip instances.seq )
          yield renaming compose Substitution( eigenVariable -> term )

      eliminateMerges( ExpansionProofWithCut(
        ( for ( ( subst, ( term, instance ) ) <- substs zip instances.toSeq ) yield subst(
          if ( instance.polarity ) ETImp( instance, child ) else ETImp( child, instance )
        ).asInstanceOf[ETImp] )
          ++ ( for ( c <- rest; s <- substs ) yield s( c ).asInstanceOf[ETImp] ),
        for ( tree <- expansionSequent ) yield ETMerge( substs.map { _( tree ) } )
      ) )
    }

    ( cut1, cut2 ) match {
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

object ExpansionProofToLK {
  /**
   * Translate an expansion proof to LK.
   *
   * @param ep an expansion sequent whose deep sequent is a propositional tautology
   * @return an LKProof of the shallow sequent of ep
   */
  def apply( ep: ExpansionProof, hasEquality: Boolean = false ): LKProof =
    solve.expansionProofToLKProof( ep.expansionSequent, if ( hasEquality ) Some( Escargot ) else None ).get
}
