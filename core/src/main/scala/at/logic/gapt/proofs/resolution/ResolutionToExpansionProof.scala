package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifierOnLogicalLevel
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable

object ResolutionToExpansionProof {

  def apply( proof: ResolutionProof ): ExpansionProof = {
    val expansionWithDefs = withDefs( proof )
    val containsEquality = proof.subProofs.exists {
      case Refl( _ )                   => true
      case Paramod( _, _, _, _, _, _ ) => true
      case _                           => false
    }
    val defConsts = proof.subProofs collect { case d: DefIntro => d.defConst: Const }
    eliminateCutsET( eliminateDefsET( eliminateCutsET( expansionWithDefs ), !containsEquality, defConsts ) )
  }

  private implicit class RichPair[A, B]( val pair: ( A, B ) ) extends AnyVal {
    def map1[A_]( f: A => A_ ): ( A_, B ) = ( f( pair._1 ), pair._2 )
    def map2[B_]( f: B => B_ ): ( A, B_ ) = ( pair._1, f( pair._2 ) )
  }

  def withDefs( proof: ResolutionProof ): ExpansionProofWithCut = {
    val nameGen = rename.awayFrom( proof.subProofs.flatMap( _.conclusion.elements ).flatMap( variables( _ ) ) )

    val expansions = mutable.Map[ResolutionProof, Set[( Substitution, ExpansionSequent )]]().withDefaultValue( Set() )

    val cuts = mutable.Buffer[ETImp]()
    var expansionSequent: ExpansionSequent =
      proof.conclusion.map( _.asInstanceOf[HOLAtom] ).map( ETAtom( _, false ), ETAtom( _, true ) )
    val splitDefn = mutable.Map[HOLAtom, HOLFormula]()
    val splitCutL = mutable.Map[HOLAtom, List[ExpansionTree]]().withDefaultValue( Nil )
    val splitCutR = mutable.Map[HOLAtom, List[ExpansionTree]]().withDefaultValue( Nil )

    def propg_( p: ResolutionProof, q: ResolutionProof, f: Set[( Substitution, ExpansionSequent )] => Set[( Substitution, ExpansionSequent )] ) = {
      val newEs = f( expansions( p ) )
      for ( ( s, e ) <- newEs ) {
        for ( et <- e.antecedent ) require( et.polarity )
        for ( et <- e.succedent ) require( !et.polarity )
        require( e.shallow == s( q.conclusion ) )
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
      Set( Substitution() -> sequent.map( _.asInstanceOf[HOLAtom] ).map( ETAtom( _, true ), ETAtom( _, false ) ) )

    expansions( proof ) = sequent2expansions( proof.conclusion )

    proof.dagLike.postOrder.reverse.foreach {
      case p @ Input( Sequent( Seq( f ), Seq() ) ) if freeVariables( f ).isEmpty =>
        expansionSequent :+= ETMerge( f, true, expansions( p ).map( _._2.elements.head ) )
        clear( p )
      case p @ Input( Sequent( Seq(), Seq( f ) ) ) if freeVariables( f ).isEmpty =>
        expansionSequent +:= ETMerge( f, false, expansions( p ).map( _._2.elements.head ) )
        clear( p )
      case p @ Input( seq ) =>
        val fvs = freeVariables( seq ).toSeq
        val sh = All.Block( fvs, seq.toDisjunction )
        expansionSequent +:= ETWeakQuantifierBlock( sh, fvs.size,
          for ( ( subst, es ) <- expansions( p ) ) yield subst( fvs ) -> es.toDisjunction( false ) )
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
      case p @ Resolution( q1, i1, q2, i2 ) =>
        val atom = q1.conclusion( i1 ).asInstanceOf[HOLAtom]
        val Seq( oc1, oc2 ) = p.occConnectors
        propg_( p, q1, _.map( es => es._1 -> oc1.parent( es._2, ETAtom( es._1( atom ).asInstanceOf[HOLAtom], false ) ) ) )
        propg( p, q2, _.map( es => es._1 -> oc2.parent( es._2, ETAtom( es._1( atom ).asInstanceOf[HOLAtom], true ) ) ) )
      case p @ DefIntro( q, i, defAtom, definition ) =>
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( es => es._1 -> oc.parent( es._2 ).updated( i, ETDefinedAtom( es._1( defAtom ).asInstanceOf[HOLAtom], i.isAnt, definition ) ) ) )

      case p @ Paramod( q1, i1, ltr, q2, i2, ctx ) =>
        val Seq( oc1, oc2 ) = p.occConnectors
        propg_( p, q1, _.map( es => es._1 -> oc1.parent( es._2 ).updated( i1, ETAtom( es._1( q1.conclusion( i1 ) ).asInstanceOf[HOLAtom], false ) ) ) )
        propg( p, q2, _.map( es => es._1 -> oc2.parent( es._2 ).updated( i2, replaceWithContext( es._2( p.mainIndices.head ), es._1( ctx ).asInstanceOf[Abs], es._1( p.t ) ) ) ) )

      case p @ AvatarSplit( q, components ) =>
        val renaming = Substitution( for ( v <- freeVariables( q.conclusion ) ) yield v -> nameGen.fresh( v ) )
        for ( AvatarSplit.QuantComponent( qca @ AvatarQuantComponentAtom( splAtom, clause ), subst ) <- components ) {
          val All.Block( vs, c ) = qca.definition
          splitDefn( splAtom ) = qca.definition
          splitCutL( splAtom ) ::= ETStrongQuantifierBlock(
            qca.definition,
            renaming( subst( vs ) ).map( _.asInstanceOf[Var] ),
            formulaToExpansionTree( renaming( subst( c ) ), true )
          )
        }
        propg( p, q, _ => for ( ( _, es ) <- sequent2expansions( q.conclusion ) ) yield renaming -> renaming( es ) )
      case p @ AvatarComponent( AvatarComponent.PropComponent( _, _ ) ) =>
        clear( p )
      case p @ AvatarComponent( AvatarComponent.QuantComponent( qca @ AvatarQuantComponentAtom( splAtom, comp ) ) ) =>
        val defn @ All.Block( vs, _ ) = qca.definition
        splitDefn( splAtom ) = defn
        splitCutR( splAtom ) ::= ETWeakQuantifierBlock(
          defn, vs.size,
          for ( ( s, es ) <- expansions( p ) )
            yield s( vs ) -> es.toDisjunction( false )
        )
        clear( p )
      case p @ AvatarAbsurd( q ) =>
        propg( p, q, _ => sequent2expansions( q.conclusion ) )

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
      case p: AndR1 => prop1s( p, ( s, et ) => ETAnd( et, ETWeakening( s( p.sub2 ), false ) ) )
      case p: OrL1  => prop1s( p, ( s, et ) => ETOr( et, ETWeakening( s( p.sub2 ), true ) ) )
      case p: ImpL1 => prop1s( p, ( s, et ) => ETImp( et, ETWeakening( s( p.sub2 ), true ) ) )
      case p: AndR2 => prop1s( p, ( s, et ) => ETAnd( ETWeakening( s( p.sub1 ), false ), et ) )
      case p: OrL2  => prop1s( p, ( s, et ) => ETOr( ETWeakening( s( p.sub1 ), true ), et ) )
      case p: ImpL2 => prop1s( p, ( s, et ) => ETImp( ETWeakening( s( p.sub1 ), false ), et ) )
      case p: WeakQuantResolutionRule =>
        val Seq( oc ) = p.occConnectors
        val subFVs = freeVariables( p.subProof.conclusion )
        propg( p, p.subProof, _.groupBy( _._1.restrict( subFVs ) ).mapValues( ess =>
          for ( i <- p.subProof.conclusion.indicesSequent ) yield if ( i == p.idx ) ETWeakQuantifier(
            ess.head._1.restrict( subFVs )( p.subProof.conclusion( p.idx ) ),
            ess.groupBy( _._1( p.variable ) ).mapValues( _.map( _._2( oc.child( i ) ) ) ).mapValues( ETMerge( _ ) )
          )
          else ETMerge( ess.map( _._2 ).map( _( oc.child( i ) ) ) ) ).toSet )

      case p: SkolemQuantResolutionRule =>
        prop1s( p, ( s, et ) => ETSkolemQuantifier( s( p.subProof.conclusion( p.idx ) ), s( p.skolemTerm ), p.skolemDef, et ) )
    }

    for ( ( splAtom, defn ) <- splitDefn )
      cuts += ETImp( ETMerge( defn, true, splitCutL( splAtom ) ), ETMerge( defn, false, splitCutR( splAtom ) ) )

    eliminateMerges( ExpansionProofWithCut( cuts, expansionSequent ) )
  }
}