package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifierOnLogicalLevel
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable

/**
 * Converts a resolution proof to an expansion proof.*
 * ResolutionToExpansionProof( rp ) will return the expansion proof of rp and ResolutionToExpansionProof( rp, input )
 * is used by the CERES method to return the expansion proof of the ACNF, which is extracted from the proof projections.
 *
 * Let us first ignore splitting and subformula definitions for simplicity.
 * However we may still have clausification inferences.
 * The conversion then proceeds bottom-up through the resolution proof (to be precise: in a reverse post-order traversal).
 *
 * At each point in the algorithm, we associate with every subproof a set of expansion sequents and associated substitutions,
 * i.e. we keep a `Map[ResolutionProof, Set[(Substitution, ExpansionSequent)] ]` with the following properties:
 * 1. the conjunction of all deep sequents (each interpreted as a disjunction) is unsatisfiable, and
 * 2. the substitution applied to the shallow sequent is always equal to the conclusion of the subproof.
 *
 * In every step we consider a subproof, empty its `Set[(Substitution, ExpansionSequent)]`,
 * and add in exchange the appropriate sets to its premises, while keeping the invariant.  In this manner,
 * these sets propagate upwards through the proof to the input sequents.
 *
 * Let us first consider the common case that the input sequents are ground unit sequents: i.e. if we obtained a resolution
 * proof for `∀x A(x), ∀x B(x) :- ∀x C(x)`, then we would have the input sequents `:- ∀x A(x)`, `:- ∀x B(x)`, and `∀x C(x) :-`.
 * When we have finally propagated all the sets up to the input sequents, the invariant guarantees the following:
 * we have expansion sequents with the input sequents as shallow sequents (at this point we use the
 * requirement that the input sequents are ground), such that the conjunction of the deep sequents
 * (interpreted as disjunctions) is unsatisfiable.
 * This immediately implies that if we combine the expansions of the input sequents into a sequent, we get an
 * expansion proof of `∀x A(x), ∀x B(x) :- ∀x C(x)`.
 *
 * In the unlikely case that the resolution proof starts from clauses, we just pretend that the clauses are derived
 * from formulas--that is, we instead of beginning with `D(x), E(x,y) :- F(y)` we just imagine the proof begins with
 * `:- ∀x ∀y (¬D(x) ∨ ¬E(x,y) ∨ F(y))`.
 *
 * Splitting inferences are converted to cuts in the expansion proof: formally, we can first skip all the splitting
 * inferences in the resoltion proof; the assertions now become part of the clauses, and we get additional input sequents.
 * For example, consider the clauses `:- A(x), B(y)`, `A(c) :-`, and `B(c) :-`.  The natural way to refute these clauses
 * is to split the first clause into `:- A(x) <-- s1` and `:- B(y) <-- s2`, then perform unit resolution twice, and
 * then have a propositional contradiction.  After skipping the splitting inferences we would get a proof starting from
 * `:- s1, s2`, `s1 :- A(x)`, `s2 :- B(x)`, `A(c) :-`, and `B(c) :-`.  If we replace `s1 := ∀x A(x)` and `s2 := ∀x B(x)`
 * everywhere in the resulting expansion proof, then we can package up the expansions of `s1 :- A(x)` and `s2 :- B(x)` as cuts.
 * The other clauses are then precisely the clause we had before splitting.
 *
 * Subformula definitions are eliminated after the conversion to expansion proofs, see [[eliminateDefsET]].
 */
object ResolutionToExpansionProof {

  def apply( proof: ResolutionProof ): ExpansionProof = {
    apply( proof, inputsAsExpansionSequent )
  }

  def inputsAsExpansionSequent( input: Input, set: Set[( Substitution, ExpansionSequent )] ): ExpansionSequent = {
    input match {
      case ( Input( Sequent( Seq( f ), Seq() ) ) ) if freeVariables( f ).isEmpty =>
        Sequent() :+ ( ETMerge( f, Polarity.InSuccedent, set.map( _._2.elements.head ) ) )

      case ( Input( Sequent( Seq(), Seq( f ) ) ) ) if freeVariables( f ).isEmpty =>
        Sequent().+:( ETMerge( f, Polarity.InAntecedent, set.map( _._2.elements.head ) ) )

      case ( Input( seq ) ) =>
        val fvs = freeVariables( seq ).toSeq
        val sh = All.Block( fvs, seq.toDisjunction )
        Sequent().+:( ETWeakQuantifierBlock( sh, fvs.size,
          for ( ( subst, es ) <- set ) yield subst( fvs ) -> es.toDisjunction( Polarity.Negative ) ) )
    }
  }

  def apply( proof: ResolutionProof, input: ( Input, Set[( Substitution, ExpansionSequent )] ) => ExpansionSequent ): ExpansionProof = {
    val expansionWithDefs = withDefs( proof, input )
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
  def withDefs( proof: ResolutionProof, input: ( Input, Set[( Substitution, ExpansionSequent )] ) => ExpansionSequent, addConclusion: Boolean = true ): ExpansionProofWithCut = {
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

    def perfMerges( expansionSequent: ExpansionSequent ): ExpansionSequent = {
      expansionSequent.groupBy( _.shallow ).map( ets => ETMerge( ets._2 ) )
    }
    expansions( proof ) = sequent2expansions( proof.conclusion )

    proof.dagLike.postOrder.reverse.foreach {
      case p @ Input( seq ) =>
        expansionSequent ++= input( Input( seq ), expansions( p ) )
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
      case p @ DefIntro( q, i, definition, repContext ) =>
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( es => es._1 -> oc.parent( es._2 ).updated( i, ETDefinedAtom( es._1( p.defAtom ).asInstanceOf[HOLAtom], !i.polarity, p.by ) ) ) )

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

    eliminateMerges( ExpansionProofWithCut( cuts, perfMerges( expansionSequent ) ) )
  }
}