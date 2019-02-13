package gapt.proofs.resolution

import gapt.expr._
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.proofs.expansion._
import gapt.provers.sat.Sat4j
import gapt.utils.Maybe

import scala.collection.mutable

/**
 * Converts a resolution proof to an expansion proof.
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
 * Subformula definitions are eliminated after the conversion to expansion proofs, see
 * [[gapt.proofs.expansion.eliminateDefsET]].
 */
object ResolutionToExpansionProof {

  def apply( proof: ResolutionProof )( implicit ctx: Maybe[Context] ): ExpansionProof = {
    apply( proof, inputsAsExpansionSequent )
  }

  def inputsAsExpansionSequent( input: Input, set: Set[( Substitution, ExpansionSequent )] ): ExpansionSequent = {
    input match {
      case Input( Sequent( Seq( f ), Seq() ) ) if freeVariables( f ).isEmpty =>
        Sequent() :+ ETMerge( f, Polarity.InSuccedent, set.map( _._2.elements.head ) )

      case Input( Sequent( Seq(), Seq( f ) ) ) if freeVariables( f ).isEmpty =>
        ETMerge( f, Polarity.InAntecedent, set.map( _._2.elements.head ) ) +: Sequent()

      case Input( seq ) =>
        val fvs = freeVariables( seq ).toSeq
        val sh = All.Block( fvs, seq.toDisjunction )
        ETWeakQuantifierBlock( sh, fvs.size,
          for ( ( subst, es ) <- set ) yield subst( fvs ) -> es.toDisjunction( Polarity.Negative ) ) +: Sequent()
    }
  }

  def apply(
    proof: ResolutionProof,
    input: ( Input, Set[( Substitution, ExpansionSequent )] ) => ExpansionSequent )(
    implicit
    ctx: Maybe[Context] ): ExpansionProof = {
    implicit val ctx1: Context = ctx.getOrElse( MutableContext.guess( proof ) )
    val expansionWithDefs = withDefs( proof, input )
    val defConsts = proof.subProofs collect { case d: DefIntro => d.defConst: Const }
    eliminateCutsET( eliminateDefsET( eliminateCutsET( expansionWithDefs ), !containsEquationalReasoning( proof ), defConsts ) )
  }

  private implicit class RichPair[A, B]( private val pair: ( A, B ) ) extends AnyVal {
    def map1[A_]( f: A => A_ ): ( A_, B ) = ( f( pair._1 ), pair._2 )
    def map2[B_]( f: B => B_ ): ( A, B_ ) = ( pair._1, f( pair._2 ) )
  }

  private val debugCheckTyping = false
  private val debugCheckTautology = false

  /**
   * Performs the conversion without eliminating the definitions
   * introduced by structural clausification.
   */
  def withDefs(
    proof:         ResolutionProof,
    input:         ( Input, Set[( Substitution, ExpansionSequent )] ) => ExpansionSequent,
    addConclusion: Boolean                                                                = true ): ExpansionProof = {
    val nameGen = rename.awayFrom( containedNames( proof ) )

    val expansions = mutable.Map[ResolutionProof, Set[( Substitution, Sequent[ETt] )]]().withDefaultValue( Set() )

    val cuts = mutable.Buffer[ETCut.Cut]()
    var expansionSequent: ExpansionSequent =
      if ( !addConclusion ) Sequent()
      else proof.conclusion.zipWithIndex.map { case ( a, i ) => ETAtom( a.asInstanceOf[Atom], !i.polarity ) }
    val splitDefn = mutable.Map[Atom, Formula]()
    val splitCutL = mutable.Map[Atom, List[ExpansionTree]]().withDefaultValue( Nil )
    val splitCutR = mutable.Map[Atom, List[ExpansionTree]]().withDefaultValue( Nil )

    def mkExpSeq( p: ResolutionProof, s: Substitution, ts: Sequent[ETt] ): ExpansionSequent =
      for ( ( ( f, t ), i ) <- p.conclusion.zip( ts ).zipWithIndex )
        yield ExpansionTree( BetaReduction.betaNormalize( s( f ) ), !i.polarity, t )

    def propg_( p: ResolutionProof, q: ResolutionProof,
                f: Set[( Substitution, Sequent[ETt] )] => Set[( Substitution, Sequent[ETt] )] ) = {
      val fvsQ = freeVariables( q.conclusion )
      val newEs = f( expansions( p ) ).map( _.map1( _.restrict( fvsQ ) ) )
      if ( debugCheckTyping ) for ( ( s, e ) <- newEs ) mkExpSeq( q, s, e ).foreach( _.check() )
      expansions( q ) = expansions( q ) union newEs
    }
    def propg( p: ResolutionProof, q: ResolutionProof,
               f: Set[( Substitution, Sequent[ETt] )] => Set[( Substitution, Sequent[ETt] )] ) = {
      propg_( p, q, f )
      clear( p )
    }
    def clear( p: ResolutionProof ) = {
      expansions -= p
      if ( debugCheckTautology ) { // expensive invariant check
        val deepExpansions = for {
          ( q, exp ) <- expansions
          ( subst, es ) <- exp
        } yield ( q.assertions ++ mkExpSeq( q, subst, es ).deep ).toDisjunction
        val splitL = for ( ( a, es ) <- splitCutL if splitDefn.contains( a ); e <- es ) yield e.deep --> a
        val splitR = for ( ( a, es ) <- splitCutR if splitDefn.contains( a ); e <- es ) yield a --> e.deep
        val deep = And( cuts.map( _.deep ) ) & And( deepExpansions ) & And( splitL ) & And( splitR ) &
          expansionSequent.deep.toNegConjunction
        require( Sat4j isUnsat deep )
      }
    }
    def propgm2( p: ResolutionProof, q: ResolutionProof, f: Sequent[ETt] => Sequent[ETt] ) =
      propg( p, q, _.map( _.map2( f ) ) )
    def prop1( p: PropositionalResolutionRule, f: ETt => ETt ) = {
      val Seq( oc ) = p.occConnectors
      propgm2( p, p.subProof, es => oc.parent( es ).updated( p.idx, f( es( p.mainIndices.head ) ) ) )
    }
    def prop1s( p: PropositionalResolutionRule, f: ( Substitution, ETt ) => ETt ) = {
      val Seq( oc ) = p.occConnectors
      propg( p, p.subProof, _.map( es => es._1 -> oc.parent( es._2 ).updated( p.idx, f( es._1, es._2( p.mainIndices.head ) ) ) ) )
    }
    def prop2( p: PropositionalResolutionRule, f: ( ETt, ETt ) => ETt ) = {
      val Seq( oc ) = p.occConnectors
      propgm2( p, p.subProof, es => oc.parent( es, f( es( p.mainIndices( 0 ) ), es( p.mainIndices( 1 ) ) ) ) )
    }

    def sequent2expansions( sequent: HOLSequent ): Set[( Substitution, Sequent[ETt] )] =
      Set( Substitution() -> sequent.map( _ => ETtAtom ) )

    expansions( proof ) = sequent2expansions( proof.conclusion )

    proof.dagLike.postOrder.reverse.foreach {
      case p @ Input( seq ) =>
        expansionSequent ++= input( Input( seq ), expansions( p ).map { case ( s, ts ) => s -> mkExpSeq( p, s, ts ) } )
        clear( p )
      case p @ Defn( _, _ ) =>
        expansionSequent +:= ExpansionTree( p.definitionFormula, Polarity.InAntecedent,
          ETtMerge( expansions( p ).map( _._2.elements.head ) ) )
        clear( p )
      case p @ Taut( f ) =>
        for {
          ( s, Sequent( Seq( l ), Seq( r ) ) ) <- expansions( p )
          if l != ETtAtom || r != ETtAtom
        } cuts += ETCut.Cut( BetaReduction.betaNormalize( s( f ) ), l, r )
        clear( p )
      case p @ Refl( _ ) =>
        clear( p )

      case p @ Factor( q, _, _ ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _ ) )
      case p @ Subst( q, subst ) =>
        val subFVs = freeVariables( q.conclusion )
        propg( p, q, _.map( _.map1( _ compose subst restrict subFVs ) ) )
      case p @ Resolution( q1, _, q2, _ ) =>
        val Seq( oc1, oc2 ) = p.occConnectors
        propg_( p, q1, _.map( es => es._1 -> oc1.parent( es._2, ETtAtom ) ) )
        propg( p, q2, _.map( es => es._1 -> oc2.parent( es._2, ETtAtom ) ) )
      case p @ DefIntro( q, i, _, _ ) =>
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( es => es._1 -> oc.parent( es._2 ).updated(
          i, ETtDef( es._1( p.defAtom ), ETtAtom ) ) ) )

      case p @ Paramod( q1, i1, _, q2, _, _ ) =>
        val Seq( oc1, oc2 ) = p.occConnectors
        propg_( p, q1, _.map( es => es._1 -> oc1.parent( es._2 ).updated( i1, ETtAtom ) ) )
        propg( p, q2, _.map( es => es._1 -> oc2.parent( es._2 ) ) )

      case p @ AvatarSplit( q, _, AvatarGroundComp( _, _ ) ) =>
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( _.map2( es => oc.parent( es, ETtAtom ) ) ) )
      case p @ AvatarSplit( q, _, comp @ AvatarNonGroundComp( splAtom, definition, vars ) ) =>
        val renaming = Substitution( for ( v <- freeVariables( comp.clause ) ) yield v -> nameGen.fresh( v ) )
        splitDefn( splAtom ) = definition
        splitCutL( splAtom ) ::= ETStrongQuantifierBlock(
          definition,
          renaming( vars ).map( _.asInstanceOf[Var] ),
          formulaToExpansionTree( renaming( comp.disjunction ), Polarity.InSuccedent ) )
        val Seq( oc ) = p.occConnectors
        propg( p, q, _.map( es => renaming.compose( es._1 ) -> oc.parents( es._2 ).zipWithIndex.map {
          case ( Seq( et ), _ ) => et
          case ( Seq(), _ )     => ETtAtom
        } ) )
      case p @ AvatarComponent( AvatarGroundComp( _, _ ) ) =>
        clear( p )
      case p @ AvatarComponent( AvatarNegNonGroundComp( _, _, _, _ ) ) =>
        clear( p )
      case p @ AvatarComponent( AvatarNonGroundComp( splAtom, definition, vars ) ) =>
        splitDefn( splAtom ) = definition
        splitCutR( splAtom ) ::= ETWeakQuantifierBlock(
          definition, vars.size,
          for ( ( s, es0 ) <- expansions( p ); es = mkExpSeq( p, s, es0 ) )
            yield s( vars ) -> es.toDisjunction( Polarity.Negative ) )
        clear( p )
      case p @ AvatarContradiction( q ) =>
        propg( p, q, _ => sequent2expansions( q.conclusion ) )

      case p: Flip =>
        prop1( p, { case ETtAtom => ETtAtom case _ => throw new IllegalArgumentException } )

      case p @ TopL( q, _ ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _, ETtNullary ) )
      case p @ BottomR( q, _ ) =>
        val Seq( oc ) = p.occConnectors
        propgm2( p, q, oc.parent( _, ETtNullary ) )
      case p: NegL  => prop1( p, ETtUnary )
      case p: NegR  => prop1( p, ETtUnary )
      case p: AndL  => prop2( p, ETtBinary )
      case p: OrR   => prop2( p, ETtBinary )
      case p: ImpR  => prop2( p, ETtBinary )
      case p: AndR1 => prop1( p, ETtBinary( _, ETtWeakening ) )
      case p: OrL1  => prop1( p, ETtBinary( _, ETtWeakening ) )
      case p: ImpL1 => prop1( p, ETtBinary( _, ETtWeakening ) )
      case p: AndR2 => prop1( p, ETtBinary( ETtWeakening, _ ) )
      case p: OrL2  => prop1( p, ETtBinary( ETtWeakening, _ ) )
      case p: ImpL2 => prop1( p, ETtBinary( ETtWeakening, _ ) )
      case p: WeakQuantResolutionRule =>
        val Seq( oc ) = p.occConnectors
        val subFVs = freeVariables( p.subProof.conclusion )
        propg( p, p.subProof, _.groupBy( _._1.restrict( subFVs ) ).mapValues( ess =>
          for ( i <- p.subProof.conclusion.indicesSequent; j = oc.child( i ) )
            yield if ( i == p.idx )
            ETtWeak( Map() ++ ess.groupBy( _._1( p.variable ) ).mapValues( _.map( _._2( j ) ) ).mapValues( ETtMerge( _ ) ) )
          else
            ETtMerge( ess.map( _._2( j ) ) ) ).toSet )

      case p: SkolemQuantResolutionRule =>
        prop1s( p, ( s, et ) => ETtSkolem( s( p.skolemTerm ), et ) )
    }

    for ( ( splAtom, defn ) <- splitDefn )
      cuts += (
        ETMerge( defn, Polarity.InSuccedent, splitCutL( splAtom ) ) ->
        ETMerge( defn, Polarity.InAntecedent, splitCutR( splAtom ) ) )

    ExpansionProof( eliminateMerges( ETMerge( ETCut( cuts ) +: expansionSequent ) ) )
  }
}