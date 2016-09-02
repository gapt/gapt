package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.Context.Definition
import at.logic.gapt.proofs.{ Ant, OccConnector, Sequent, SequentIndex, Suc }
import at.logic.gapt.proofs.lk._

import scala.collection.mutable
import scalaz.\/-

object ResolutionToLKProof {

  def apply( proof: ResolutionProof ): LKProof = {
    val lk = apply( proof, in => in.sequent match {
      case Sequent( Seq(), Seq( f ) ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case Sequent( Seq( f ), Seq() ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case seq =>
        val fvs = freeVariables( seq ).toSeq
        val \/-( proj ) = solvePropositional( seq.toDisjunction +: seq )
        ForallLeftBlock( proj, All.Block( fvs, seq.toDisjunction ), fvs )
    } )
    if ( proof.definitions.isEmpty ) lk
    else DefinitionElimination( proof.definitions )( lk )
  }

  def asDerivation( proof: ResolutionProof ): LKProof =
    apply( proof, in => TheoryAxiom( in.sequent.map( _.asInstanceOf[HOLAtom] ) ) )

  def apply( proof: ResolutionProof, input: Input => LKProof ): LKProof = {
    val memo = mutable.Map[ResolutionProof, LKProof]()

    def reducef( p: PropositionalResolutionRule )( func: HOLFormula => LKProof ) = {
      val q = f( p.subProof )
      reduceAxiom( q, q.conclusion.indexOfPol( p.subProof.conclusion( p.idx ), p.idx.polarity ) )( func )
    }

    def contract( p: ResolutionProof, q: LKProof ) =
      ContractionMacroRule( q, ( ( p.conclusion ++ p.assertions ) diff q.endSequent.distinct ) ++ q.endSequent.distinct )

    def f( p: ResolutionProof ): LKProof = memo.getOrElseUpdate( p, contract( p, p match {
      case in: Input       => input( in )
      case Taut( formula ) => LogicalAxiom( formula )
      case Refl( term )    => ReflexivityAxiom( term )

      case p @ Defn( defConst, defExpr ) =>
        val phi = BetaReduction.betaNormalize( defExpr( p.vars ) ).asInstanceOf[HOLFormula]
        val definition = Definition( defConst, defExpr )
        val ctx = replacementContext.abstractTerm( defConst( p.vars: _* ) )( defConst )

        ProofBuilder.
          c( LogicalAxiom( phi ) ).
          u( DefinitionLeftRule( _, Ant( 0 ), definition, ctx ) ).
          u( ImpRightRule( _, Ant( 0 ), Suc( 0 ) ) ).
          c( LogicalAxiom( phi ) ).
          u( DefinitionRightRule( _, Suc( 0 ), definition, ctx ) ).
          u( ImpRightRule( _, Ant( 0 ), Suc( 0 ) ) ).
          b( AndRightRule( _, Suc( 0 ), _, Suc( 0 ) ) ).
          u( ForallRightBlock( _, p.definitionFormula, p.vars ) ).
          qed

      case Factor( q, i1, i2 ) =>
        if ( i1 isAnt )
          ContractionLeftRule( f( q ), q.conclusion( i1 ) )
        else
          ContractionRightRule( f( q ), q.conclusion( i1 ) )
      case Resolution( q1, i1, q2, i2 ) =>
        CutRule( f( q1 ), f( q2 ), q1.conclusion( i1 ) )
      case Subst( q, subst ) =>
        subst( f( q ) )
      case p @ Paramod( q1, i1, ltr, q2, i2, ctx: Abs ) =>
        if ( i2 isAnt )
          ParamodulationLeftRule( f( q1 ), q1.conclusion( i1 ), f( q2 ), q2.conclusion( i2 ), ctx )
        else
          ParamodulationRightRule( f( q1 ), q1.conclusion( i1 ), f( q2 ), q2.conclusion( i2 ), ctx )

      case p @ AvatarContradiction( q ) => f( q )
      case AvatarComponent( comp @ AvatarNonGroundComp( splAtom, aux, vars ) ) =>
        val \/-( p1 ) = solvePropositional( comp.disjunction +: comp.clause )
        val p2 = ForallLeftBlock( p1, aux, vars )

        val p3 = DefinitionLeftRule( p2, aux, comp.toDefinition, splAtom )
        p3
      case AvatarComponent( AvatarGroundComp( atom, _ ) ) => LogicalAxiom( atom )
      case AvatarComponent( comp @ AvatarNegNonGroundComp( splAtom, aux, vars, idx ) ) =>
        val \/-( p1 ) = solvePropositional( comp.clause :+ comp.disjunction )
        val p2 = ForallRightBlock( p1, aux, vars )
        val p3 = DefinitionRightRule( p2, aux, comp.toDefinition, splAtom )
        p3
      case AvatarSplit( q, indices, AvatarGroundComp( _, _ ) ) => f( q )
      case p @ AvatarSplit( q, _, comp @ AvatarNonGroundComp( splAtom, aux, vars ) ) =>
        var p_ = f( q )
        for {
          a <- comp.clause.antecedent
          if p_.conclusion.antecedent contains a
        } p_ = NegRightRule( p_, a )
        def mkOr( lits: HOLFormula ): Unit =
          lits match {
            case Or( lits_, lit ) =>
              mkOr( lits_ )
              p_ = OrRightMacroRule( p_, lits_, lit )
            case lit =>
              if ( !p_.conclusion.succedent.contains( lit ) )
                p_ = WeakeningRightRule( p_, lit )
          }
        mkOr( comp.disjunction )
        p_ = ForallRightBlock( p_, aux, vars )
        p_ = DefinitionRightRule( p_, aux, comp.toDefinition, splAtom )
        p_

      case DefIntro( q, i: Suc, definition, args ) =>
        val Definition( what, by ) = definition
        val tp = what.exptype
        val X = rename awayFrom freeVariables( args ) fresh Var( "X", tp )
        val ctx = Abs( X, Apps( X, args ) )
        DefinitionRightRule( f( q ), q.conclusion( i ), definition, ctx )

      case DefIntro( q, i: Ant, definition, args ) =>
        val Definition( what, by ) = definition
        val tp = what.exptype
        val X = rename awayFrom freeVariables( args ) fresh Var( "X", tp )
        val ctx = Abs( X, Apps( X, args ) )
        DefinitionLeftRule( f( q ), q.conclusion( i ), definition, ctx )

      case p @ Flip( q, i: Ant ) =>
        CutRule( mkSymmProof( p.s, p.t ), f( q ), q.conclusion( i ) )
      case p @ Flip( q, i: Suc ) =>
        CutRule( f( q ), mkSymmProof( p.t, p.s ), q.conclusion( i ) )

      case p: TopL    => reducef( p ) { _ => TopAxiom }
      case p: BottomR => reducef( p ) { _ => BottomAxiom }
      case p: NegL    => reducef( p ) { case Neg( l ) => NegRightRule( LogicalAxiom( l ), Ant( 0 ) ) }
      case p: NegR    => reducef( p ) { case Neg( l ) => NegLeftRule( LogicalAxiom( l ), Suc( 0 ) ) }
      case p: AndL    => reducef( p ) { case And( l, r ) => AndRightRule( LogicalAxiom( l ), Suc( 0 ), LogicalAxiom( r ), Suc( 0 ) ) }
      case p: AndR1   => reducef( p ) { case And( l, r ) => AndLeftRule( WeakeningLeftRule( LogicalAxiom( l ), r ), Ant( 1 ), Ant( 0 ) ) }
      case p: AndR2   => reducef( p ) { case And( l, r ) => AndLeftRule( WeakeningLeftRule( LogicalAxiom( r ), l ), Ant( 0 ), Ant( 1 ) ) }
      case p: OrR     => reducef( p ) { case Or( l, r ) => OrLeftRule( LogicalAxiom( l ), Ant( 0 ), LogicalAxiom( r ), Ant( 0 ) ) }
      case p: OrL1    => reducef( p ) { case Or( l, r ) => OrRightRule( WeakeningRightRule( LogicalAxiom( l ), r ), Suc( 0 ), Suc( 1 ) ) }
      case p: OrL2    => reducef( p ) { case Or( l, r ) => OrRightRule( WeakeningRightRule( LogicalAxiom( r ), l ), Suc( 1 ), Suc( 0 ) ) }
      case p: ImpR    => reducef( p ) { case Imp( l, r ) => ImpLeftRule( LogicalAxiom( l ), Suc( 0 ), LogicalAxiom( r ), Ant( 0 ) ) }
      case p: ImpL1   => reducef( p ) { case Imp( l, r ) => ImpRightRule( WeakeningRightRule( LogicalAxiom( l ), r ), Ant( 0 ), Suc( 1 ) ) }
      case p: ImpL2   => reducef( p ) { case Imp( l, r ) => ImpRightRule( WeakeningLeftRule( LogicalAxiom( r ), l ), Ant( 0 ), Suc( 0 ) ) }

      case p: AllL    => reducef( p )( f => ForallSkRightRule( LogicalAxiom( instantiate( f, p.skolemTerm ) ), Suc( 0 ), f, p.skolemTerm, p.skolemDef ) )
      case p: ExR     => reducef( p )( f => ExistsSkLeftRule( LogicalAxiom( instantiate( f, p.skolemTerm ) ), Ant( 0 ), f, p.skolemTerm, p.skolemDef ) )

      case p: AllR    => reducef( p )( f => ForallLeftRule( LogicalAxiom( instantiate( f, p.variable ) ), f, p.variable ) )
      case p: ExL     => reducef( p )( f => ExistsRightRule( LogicalAxiom( instantiate( f, p.variable ) ), f, p.variable ) )
    } ) )

    f( proof )
  }

  /**
   * Transforms e.g. a proof of  Γ :- Δ, φ ∧ ψ  to one of  Γ :- Δ, φ  without introducing a cut.
   *
   * Assumes that only contractions and logical axioms operate on (ancestors
   * of) the formula, and that func(φ ∧ ψ) is a proof of φ ∧ ψ :- φ.
   */
  def reduceAxiom( proof: LKProof, idx: SequentIndex )( func: HOLFormula => LKProof ): LKProof =
    new LKVisitor[Sequent[Boolean]] {
      val formula = proof.conclusion( idx )
      val proofToInsert = func( formula )
      val connToInsert = OccConnector( proofToInsert.endSequent, formula +: Sequent() :+ formula,
        for ( i <- proofToInsert.endSequent.indicesSequent )
          yield if ( proofToInsert.endSequent( i ) == formula )
          Seq( if ( idx.isSuc ) Ant( 0 ) else Suc( 0 ) )
        else Seq() )

      val extraSequent =
        if ( idx.isSuc ) proofToInsert.conclusion.removeFromAntecedent( formula )
        else proofToInsert.conclusion.removeFromSuccedent( formula )
      val formulaMultiplicities = Map() ++ extraSequent.polarizedElements.groupBy( identity ).mapValues( _.size )

      override def transportToSubProof( isAncestor: Sequent[Boolean], proof: LKProof, subProofIdx: Int ) =
        proof.occConnectors( subProofIdx ).parent( isAncestor, false )

      override def visitLogicalAxiom( proof: LogicalAxiom, isAncestor: Sequent[Boolean] ) =
        isAncestor.find( _ == true ) match {
          case Some( i ) => ( proofToInsert, connToInsert )
          case None      => withIdentityOccConnector( proof )
        }

      // Contract ancestors as soon as possible, and then skip the following contractions.
      override def recurse( proof: LKProof, isAncestor: Sequent[Boolean] ): ( LKProof, OccConnector[HOLFormula] ) = {
        if ( isAncestor.forall( _ == false ) ) {
          ( proof, OccConnector( proof.conclusion ) )
        } else {
          val mainAncestors = proof.mainIndices.filter( isAncestor( _ ) )
          if ( !proof.isInstanceOf[LogicalAxiom] && mainAncestors.nonEmpty ) {
            val mainAncestor = mainAncestors.head
            val ( proof3, conn ) = if ( mainAncestor.isAnt ) {
              val proof2 = CutRule( LogicalAxiom( proof.conclusion( mainAncestor ) ), Suc( 0 ), proof, mainAncestor )
              recurse( proof2, proof2.getRightOccConnector.inv.parent( isAncestor, true ) )
            } else {
              val proof2 = CutRule( proof, mainAncestor, LogicalAxiom( proof.conclusion( mainAncestor ) ), Ant( 0 ) )
              recurse( proof2, proof2.getLeftOccConnector.inv.parent( isAncestor, true ) )
            }
            // FIXME: do this properly
            val proof4 = ReductiveCutElimination( proof3 )
            ( proof4, OccConnector.guessInjection( proof3.conclusion, proof4.conclusion ) * conn )
          } else {
            val ( proofNew, conn ) = super.recurse( proof, isAncestor )
            contract( proofNew, conn )
          }
        }
      }
      def contract( subProof: LKProof, subConn: OccConnector[HOLFormula] ): ( LKProof, OccConnector[HOLFormula] ) = {
        val newIndices = subConn.parentsSequent.indicesWhere( _.isEmpty )
        val newIndicesByFormula = newIndices.groupBy( i => subProof.conclusion( i ) -> i.polarity )
        newIndicesByFormula.find( ni => ni._2.size > formulaMultiplicities( ni._1 ) ) match {
          case Some( ( _, Seq( i, j, _* ) ) ) =>
            val contracted = if ( i.isSuc ) ContractionRightRule( subProof, i, j ) else ContractionLeftRule( subProof, i, j )
            ( contracted, contracted.getOccConnector * subConn )
          case None => ( subProof, subConn )
        }
      }
      override def visitContractionLeft( proof: ContractionLeftRule, isAncestor: Sequent[Boolean] ): ( LKProof, OccConnector[HOLFormula] ) =
        one2one( proof, isAncestor ) {
          case Seq( ( subProof, subConn ) ) =>
            if ( subConn.children( proof.aux1 ).isEmpty ) return ( subProof, subConn )
            ContractionLeftRule( subProof, subConn child proof.aux1, subConn child proof.aux2 )
        }
      override def visitContractionRight( proof: ContractionRightRule, isAncestor: Sequent[Boolean] ): ( LKProof, OccConnector[HOLFormula] ) =
        one2one( proof, isAncestor ) {
          case Seq( ( subProof, subConn ) ) =>
            if ( subConn.children( proof.aux1 ).isEmpty ) return ( subProof, subConn )
            ContractionRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 )
        }
    }.apply( proof, proof.conclusion.indicesSequent.map( _ == idx ) )

  /** Proof of t=s :- s=t */
  def mkSymmProof( t: LambdaExpression, s: LambdaExpression ): LKProof =
    ProofBuilder.
      c( ReflexivityAxiom( t ) ).
      u( WeakeningLeftRule( _, Eq( t, s ) ) ).
      u( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Eq( s, t ) ) ).
      qed
}
