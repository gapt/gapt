package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion._

import scala.collection.mutable

object ResolutionToExpansionProof {
  private implicit class RichPair[A, B]( val pair: ( A, B ) ) extends AnyVal {
    def map1[A_]( f: A => A_ ): ( A_, B ) = ( f( pair._1 ), pair._2 )
    def map2[B_]( f: B => B_ ): ( A, B_ ) = ( pair._1, f( pair._2 ) )
  }

  def withDefs( proof: ResolutionProof ): ExpansionProof = {
    val expansions = mutable.Map[ResolutionProof, Set[( Substitution, ExpansionSequent )]]().withDefaultValue( Set() )

    def propg( p: ResolutionProof, q: ResolutionProof, f: Set[( Substitution, ExpansionSequent )] => Set[( Substitution, ExpansionSequent )] ) =
      expansions( q ) = expansions( q ) union f( expansions( p ) )
    def propgm2( p: ResolutionProof, q: ResolutionProof, f: ExpansionSequent => ExpansionSequent ) =
      propg( p, q, _.map( _.map2( f ) ) )
    def prop1( p: PropositionalResolutionRule, f: ExpansionTree => ExpansionTree ) = {
      val Seq( oc ) = p.occConnectors
      propgm2( p, p.subProof, es => oc.parent( es ).updated( p.idx, f( es( p.mainIndices.head ) ) ) )
    }
    def prop2( p: PropositionalResolutionRule, f: ( ExpansionTree, ExpansionTree ) => ExpansionTree ) = {
      val Seq( oc ) = p.occConnectors
      propgm2( p, p.subProof, es => oc.parent( es ).updated( p.idx, f( es( p.mainIndices( 0 ) ), es( p.mainIndices( 1 ) ) ) ) )
    }

    expansions( proof ) = Set( Substitution() -> proof.conclusion.map( _.asInstanceOf[HOLAtom] ).map( ETAtom( _, true ), ETAtom( _, false ) ) )

    proof.dagLike.postOrder.reverse.foreach {
      case _: InitialClause =>

      case p @ Factor( q, i1, i2 ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _ ) )
      case p @ Subst( q, subst ) =>
        val subFVs = freeVariables( q.conclusion )
        propg( p, q, _.map( _.map1( _ compose subst restrict subFVs ) ) )
      case p @ Resolution( q1, i1, q2, i2 ) =>
        val atom = q1.conclusion( i1 ).asInstanceOf[HOLAtom]
        val Seq( oc1, oc2 ) = p.occConnectors
        propgm2( p, q1, oc1.parent( _, ETAtom( atom, false ) ) )
        propgm2( p, q2, oc2.parent( _, ETAtom( atom, true ) ) )
      case p @ DefIntro( q, i, defAtom, definition ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _ ).updated( i, ETDefinedAtom( defAtom, i.isAnt, definition ) ) )

      case p @ TopL( q, i ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _, ETTop( true ) ) )
      case p @ BottomR( q, i ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _, ETBottom( false ) ) )
      case p: NegL  => prop1( p, ETNeg( _ ) )
      case p: NegR  => prop1( p, ETNeg( _ ) )
      case p: AndL  => prop2( p, ETAnd( _, _ ) )
      case p: OrR   => prop2( p, ETOr( _, _ ) )
      case p: ImpR  => prop2( p, ETImp( _, _ ) )
      case p: AndR1 => prop1( p, ETAnd( _, ETWeakening( p.sub2, false ) ) )
      case p: AndR2 => prop1( p, ETAnd( ETWeakening( p.sub1, false ), _ ) )
      case p: OrL1  => prop1( p, ETOr( _, ETWeakening( p.sub2, true ) ) )
      case p: OrL2  => prop1( p, ETOr( ETWeakening( p.sub1, true ), _ ) )
      case p: ImpL1 => prop1( p, ETImp( _, ETWeakening( p.sub2, true ) ) )
      case p: ImpL2 => prop1( p, ETImp( ETWeakening( p.sub1, false ), _ ) )

      case p: WeakQuantResolutionRule =>
        val Seq( oc ) = p.occConnectors
        val subFVs = freeVariables( p.subProof.conclusion )
        propg( p, p.subProof, _.groupBy( _._1.restrict( subFVs ) ).mapValues( ess =>
          for ( i <- p.subProof.conclusion.indicesSequent ) yield if ( i == p.idx ) ETWeakQuantifier(
            p.subProof.conclusion( p.idx ),
            ess.groupBy( _._1( p.variable ) ).mapValues( _.map( _._2( oc.child( i ) ) ) ).mapValues( ETMerge( _ ) )
          )
          else ETMerge( ess.map( _._2 ).map( _( oc.child( i ) ) ) ) ).toSet )

      case p: SkolemQuantResolutionRule =>
        val Seq( oc ) = p.occConnectors
        prop1( p, ETSkolemQuantifier( p.subProof.conclusion( p.idx ), p.skolemTerm, p.skolemDef, _ ) )
    }

    ExpansionProof( proof.subProofs.collect {
      case p @ Input( Sequent( Seq( f ), Seq() ) ) if freeVariables( f ).isEmpty =>
        Sequent() :+ ETMerge( f, true, expansions( p ).map( _._2.elements.head ) )
      case p @ Input( Sequent( Seq(), Seq( f ) ) ) if freeVariables( f ).isEmpty =>
        ETMerge( f, false, expansions( p ).map( _._2.elements.head ) ) +: Sequent()
      case p @ Input( seq ) =>
        val fvs = freeVariables( seq ).toSeq
        val sh = All.Block( fvs, seq.toDisjunction )
        ETWeakQuantifierBlock( sh, fvs.size,
          for ( ( subst, es ) <- expansions( p ) ) yield subst( fvs ) -> es.map( ETNeg( _ ), identity ).elements.reduceOption( ETOr( _, _ ) ).getOrElse( ETBottom( false ) ) ) +: Sequent()
      case p @ Definition( _, _ ) =>
        ETMerge( p.mainFormulaSequent.elements.head, false, expansions( p ).map( _._2.elements.head ) ) +: Sequent()
    }.fold( Sequent() )( _ ++ _ ) )
  }
}