package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifierOnLogicalLevel
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable

/** Converts a resolution proof to an expansion proof. */
object ResolutionToExpansionProof {

  def apply( proof: ResolutionProof ): ExpansionProof = {
    val expansionWithDefs = withDefs( proof )
    val defConsts = proof.subProofs collect { case d: DefIntro => d.defConst: Const }
    eliminateCutsET( eliminateDefsET( eliminateCutsET( expansionWithDefs ), !containsEquationalReasoning( proof ), defConsts ) )
  }

  private implicit class RichPair[A, B]( val pair: ( A, B ) ) extends AnyVal {
    def map1[A_]( f: A => A_ ): ( A_, B ) = ( f( pair._1 ), pair._2 )
    def map2[B_]( f: B => B_ ): ( A, B_ ) = ( pair._1, f( pair._2 ) )
  }

  /**
   * Performs the conversion without eliminating the definitions
   * introduced by structural clausification.
   */
  def withDefs( proof: ResolutionProof, addConclusion: Boolean = true ): ExpansionProofWithCut = {
    val nameGen = rename.awayFrom( containedNames( proof ) )

    val expansions = mutable.Map[ResolutionProof, Set[( Substitution, ExpansionSequent )]]().withDefaultValue( Set() )

    val cuts = mutable.Buffer[ETImp]()
    var expansionSequent: ExpansionSequent =
      if ( !addConclusion ) Sequent()
      else proof.conclusion.zipWithIndex.map { case ( a, i ) => ETAtom( a.asInstanceOf[HOLAtom], !i.polarity ) }
    val splitDefn = mutable.Map[HOLAtom, HOLFormula]()
    val splitCutL = mutable.Map[HOLAtom, List[ExpansionTree]]().withDefaultValue( Nil )
    val splitCutR = mutable.Map[HOLAtom, List[ExpansionTree]]().withDefaultValue( Nil )

    def propg_( p: ResolutionProof, q: ResolutionProof, f: Set[( Substitution, ExpansionSequent )] => Set[( Substitution, ExpansionSequent )] ) = {
      val fvsQ = freeVariables( q.conclusion )
      val newEs = f( expansions( p ) ).map( _.map1( _.restrict( fvsQ ) ) )
      for ( ( s, e ) <- newEs ) {
        for ( ( et, i ) <- e.zipWithIndex ) require( et.polarity == !i.polarity )
        require( e.shallow == s( q.conclusion ).map( BetaReduction.betaNormalize ) )
      }
      expansions( q ) = expansions( q ) union newEs
    }
    def propg( p: ResolutionProof, q: ResolutionProof, f: Set[( Substitution, ExpansionSequent )] => Set[( Substitution, ExpansionSequent )] ) = {
      propg_( p, q, f )
      clear( p )
    }
    def clear( p: ResolutionProof ) = {
      expansions -= p
      if ( false ) { // expensive invariant check
        val deepExpansions = for {
          ( q, exp ) <- expansions
          ( subst, es ) <- exp
        } yield ( q.assertions ++ es.deep ).toDisjunction
        val splitL = for ( ( a, es ) <- splitCutL if splitDefn.contains( a ); e <- es ) yield e.deep --> a
        val splitR = for ( ( a, es ) <- splitCutR if splitDefn.contains( a ); e <- es ) yield a --> e.deep
        val deep = And( cuts.map( _.deep ) ) & And( deepExpansions ) & And( splitL ) & And( splitR ) & expansionSequent.deep.toNegConjunction
        require( Sat4j isUnsat deep )
      }
    }
    def propgm2( p: ResolutionProof, q: ResolutionProof, f: ExpansionSequent => ExpansionSequent ) =
      propg( p, q, _.map( _.map2( f ) ) )
    def prop1( p: PropositionalResolutionRule, f: ExpansionTree => ExpansionTree ) = {
      val Seq( oc ) = p.occConnectors
      propgm2( p, p.subProof, es => oc.parent( es ).updated( p.idx, f( es( p.mainIndices.head ) ) ) )
    }
    def prop1s( p: PropositionalResolutionRule, f: ( Substitution, ExpansionTree ) => ExpansionTree ) = {
      val Seq( oc ) = p.occConnectors
      propg( p, p.subProof, _.map( es => es._1 -> oc.parent( es._2 ).updated( p.idx, f( es._1, es._2( p.mainIndices.head ) ) ) ) )
    }
    def prop2( p: PropositionalResolutionRule, f: ( ExpansionTree, ExpansionTree ) => ExpansionTree ) = {
      val Seq( oc ) = p.occConnectors
      propgm2( p, p.subProof, es => oc.parent( es, f( es( p.mainIndices( 0 ) ), es( p.mainIndices( 1 ) ) ) ) )
    }

    def sequent2expansions( sequent: HOLSequent ): Set[( Substitution, ExpansionSequent )] =
      Set( Substitution() -> sequent.zipWithIndex.map { case ( a, i ) => ETAtom( a.asInstanceOf[HOLAtom], !i.polarity ) } )

    expansions( proof ) = sequent2expansions( proof.conclusion )

    proof.dagLike.postOrder.reverse.foreach {
      case p @ Input( Sequent( Seq( f ), Seq() ) ) if freeVariables( f ).isEmpty =>
        expansionSequent :+= ETMerge( f, Polarity.InSuccedent, expansions( p ).map( _._2.elements.head ) )
        clear( p )
      case p @ Input( Sequent( Seq(), Seq( f ) ) ) if freeVariables( f ).isEmpty =>
        expansionSequent +:= ETMerge( f, Polarity.InAntecedent, expansions( p ).map( _._2.elements.head ) )
        clear( p )
      case p @ Input( seq ) =>
        val fvs = freeVariables( seq ).toSeq
        val sh = All.Block( fvs, seq.toDisjunction )
        expansionSequent +:= ETWeakQuantifierBlock( sh, fvs.size,
          for ( ( subst, es ) <- expansions( p ) ) yield subst( fvs ) -> es.toDisjunction( Polarity.Negative ) )
        clear( p )
      case p @ Defn( _, _ ) =>
        expansionSequent +:= ETMerge( p.definitionFormula, Polarity.InAntecedent, expansions( p ).map( _._2.elements.head ) )
        clear( p )
      case p @ Taut( f ) =>
        for {
          ( s, Sequent( Seq( l ), Seq( r ) ) ) <- expansions( p )
          if !l.isInstanceOf[ETAtom] || !r.isInstanceOf[ETAtom]
        } cuts += ETImp( l, r )
        clear( p )
      case p @ Refl( _ ) =>
        clear( p )

      case p @ Factor( q, i1, i2 ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _ ) )
      case p @ Subst( q, subst ) =>
        val subFVs = freeVariables( q.conclusion )
        propg( p, q, _.map( _.map1( _ compose subst restrict subFVs ) ) )
      case p @ Resolution( q1, i1, q2, i2 ) if p.resolvedLiteral.isInstanceOf[HOLAtom] =>
        val atom = p.resolvedLiteral.asInstanceOf[HOLAtom]
        val Seq( oc1, oc2 ) = p.occConnectors
        propg_( p, q1, _.map( es => es._1 -> oc1.parent( es._2, ETAtom( es._1( atom ).asInstanceOf[HOLAtom], Polarity.InAntecedent ) ) ) )
        propg( p, q2, _.map( es => es._1 -> oc2.parent( es._2, ETAtom( es._1( atom ).asInstanceOf[HOLAtom], Polarity.InSuccedent ) ) ) )
      case p @ DefIntro( q, i, defAtom, definition ) =>
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( es => es._1 -> oc.parent( es._2 ).updated( i, ETDefinedAtom( es._1( defAtom ).asInstanceOf[HOLAtom], !i.polarity, definition ) ) ) )

      case p @ Paramod( q1, i1, ltr, q2, i2, ctx ) =>
        val Seq( oc1, oc2 ) = p.occConnectors
        propg_( p, q1, _.map( es => es._1 -> oc1.parent( es._2 ).updated( i1, ETAtom( es._1( q1.conclusion( i1 ) ).asInstanceOf[HOLAtom], Polarity.InAntecedent ) ) ) )
        propg( p, q2, _.map( es => es._1 -> oc2.parent( es._2 ).updated( i2, replaceWithContext( es._2( p.mainIndices.head ), es._1( ctx ).asInstanceOf[Abs], es._1( p.t ) ) ) ) )

      case p @ AvatarSplit( q, indices, AvatarGroundComp( atom, pol ) ) =>
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( _.map2( es => oc.parent( es, ETAtom( atom, !pol ) ) ) ) )
      case p @ AvatarSplit( q, indices, comp @ AvatarNonGroundComp( splAtom, definition, vars ) ) =>
        val renaming = Substitution( for ( v <- freeVariables( comp.clause ) ) yield v -> nameGen.fresh( v ) )
        splitDefn( splAtom ) = definition
        splitCutL( splAtom ) ::= ETStrongQuantifierBlock(
          definition,
          renaming( vars ).map( _.asInstanceOf[Var] ),
          formulaToExpansionTree( renaming( comp.disjunction ), Polarity.InSuccedent )
        )
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( es => renaming.compose( es._1 ) -> oc.parents( es._2 ).zipWithIndex.map {
          case ( Seq( et ), _ ) => et
          case ( Seq(), idx )   => ETAtom( renaming( q.conclusion( idx ) ).asInstanceOf[HOLAtom], !idx.polarity )
        } ) )
      case p @ AvatarComponent( AvatarGroundComp( _, _ ) ) =>
        clear( p )
      case p @ AvatarComponent( AvatarNegNonGroundComp( _, _, _, _ ) ) =>
        clear( p )
      case p @ AvatarComponent( AvatarNonGroundComp( splAtom, definition, vars ) ) =>
        splitDefn( splAtom ) = definition
        splitCutR( splAtom ) ::= ETWeakQuantifierBlock(
          definition, vars.size,
          for ( ( s, es ) <- expansions( p ) )
            yield s( vars ) -> es.toDisjunction( Polarity.Negative )
        )
        clear( p )
      case p @ AvatarContradiction( q ) =>
        propg( p, q, _ => sequent2expansions( q.conclusion ) )

      case p: Flip =>
        prop1( p, { case ETAtom( Eq( t, s ), pol ) => ETAtom( Eq( s, t ), pol ) } )

      case p @ TopL( q, i ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _, ETTop( !i.polarity ) ) )
      case p @ BottomR( q, i ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _, ETBottom( !i.polarity ) ) )
      case p: NegL  => prop1( p, ETNeg )
      case p: NegR  => prop1( p, ETNeg )
      case p: AndL  => prop2( p, ETAnd )
      case p: OrR   => prop2( p, ETOr )
      case p: ImpR  => prop2( p, ETImp )
      case p: AndR1 => prop1s( p, ( s, et ) => ETAnd( et, ETWeakening( s( p.sub2 ), Polarity.InAntecedent ) ) )
      case p: OrL1  => prop1s( p, ( s, et ) => ETOr( et, ETWeakening( s( p.sub2 ), Polarity.InSuccedent ) ) )
      case p: ImpL1 => prop1s( p, ( s, et ) => ETImp( et, ETWeakening( s( p.sub2 ), Polarity.InSuccedent ) ) )
      case p: AndR2 => prop1s( p, ( s, et ) => ETAnd( ETWeakening( s( p.sub1 ), Polarity.InAntecedent ), et ) )
      case p: OrL2  => prop1s( p, ( s, et ) => ETOr( ETWeakening( s( p.sub1 ), Polarity.InSuccedent ), et ) )
      case p: ImpL2 => prop1s( p, ( s, et ) => ETImp( ETWeakening( s( p.sub1 ), Polarity.InAntecedent ), et ) )
      case p: WeakQuantResolutionRule =>
        val Seq( oc ) = p.occConnectors
        val subFVs = freeVariables( p.subProof.conclusion )
        propg( p, p.subProof, _.groupBy( _._1.restrict( subFVs ) ).mapValues( ess =>
          for ( i <- p.subProof.conclusion.indicesSequent ) yield if ( i == p.idx ) ETWeakQuantifier(
            ess.head._1.restrict( subFVs )( p.subProof.conclusion( p.idx ) ),
            Map() ++ ess.groupBy( _._1( p.variable ) ).mapValues( _.map( _._2( oc.child( i ) ) ) ).mapValues( ETMerge( _ ) )
          )
          else ETMerge( ess.map( _._2 ).map( _( oc.child( i ) ) ) ) ).toSet )

      case p: SkolemQuantResolutionRule =>
        prop1s( p, ( s, et ) => ETSkolemQuantifier( s( p.subProof.conclusion( p.idx ) ), s( p.skolemTerm ), p.skolemDef, et ) )
    }

    for ( ( splAtom, defn ) <- splitDefn )
      cuts += ETImp(
        ETMerge( defn, Polarity.InSuccedent, splitCutL( splAtom ) ),
        ETMerge( defn, Polarity.InAntecedent, splitCutR( splAtom ) )
      )

    eliminateMerges( ExpansionProofWithCut( cuts, expansionSequent ) )
  }
}