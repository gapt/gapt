package gapt.proofs.resolution

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.hol.instantiate
import gapt.expr.util.freeVariables
import gapt.proofs.lk._
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.ContractionMacroRule
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.ForallRightBlock
import gapt.proofs.lk.rules.macros.OrRightMacroRule
import gapt.proofs.lk.rules.macros.ParamodulationLeftRule
import gapt.proofs.lk.rules.macros.ParamodulationRightRule
import gapt.proofs.lk.transformations.cutNormal
import gapt.proofs.lk.transformations.eliminateDefinitions
import gapt.proofs.lk.util.solvePropositional
import gapt.proofs.Ant
import gapt.proofs.ProofBuilder
import gapt.proofs.Sequent
import gapt.proofs.SequentConnector
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.RichFormulaSequent

import scala.collection.mutable

object ResolutionToLKProof {

  def withDefs( proof: ResolutionProof ): LKProof =
    apply( proof, in => in.sequent match {
      case Sequent( Seq(), Seq( f ) ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case Sequent( Seq( f ), Seq() ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case seq =>
        val fvs = freeVariables( seq ).toSeq
        val Right( proj ) = solvePropositional( seq.toDisjunction +: seq )
        ForallLeftBlock( proj, All.Block( fvs, seq.toDisjunction ), fvs )
    } )

  def apply( proof: ResolutionProof ): LKProof = {
    val lk = withDefs( proof )
    if ( proof.definitions.isEmpty ) lk
    else eliminateDefinitions( proof.definitions )( lk )
  }

  def asDerivation( proof: ResolutionProof ): LKProof =
    apply( proof, in => ProofLink( FOLAtom( "resolutionInput" ), in.sequent ) )

  def apply( proof: ResolutionProof, input: Input => LKProof ): LKProof = {
    val memo = mutable.Map[ResolutionProof, LKProof]()

    def reducef( p: PropositionalResolutionRule )( func: Formula => LKProof ) = {
      val q = f( p.subProof )
      reduceAxiom( q, q.conclusion.indexOf( p.subProof.conclusion( p.idx ), p.idx.polarity ) )( func )
    }

    def contract( p: ResolutionProof, q: LKProof ) =
      ContractionMacroRule(
        q,
        ( ( p.conclusion ++ p.assertions ) diff q.endSequent.distinct ) ++ q.endSequent.distinct )

    def f( p: ResolutionProof ): LKProof = memo.getOrElseUpdate( p, contract( p, p match {
      case in: Input       => input( in )
      case Taut( formula ) => LogicalAxiom( formula )
      case Refl( term )    => ReflexivityAxiom( term )

      case p @ Defn( defConst, defExpr ) =>
        val phi = BetaReduction.betaNormalize( defExpr( p.vars ) ).asInstanceOf[Formula]
        val defAtom = p.defConst( p.vars ).asInstanceOf[Formula]

        ProofBuilder.
          c( LogicalAxiom( phi ) ).
          u( ConversionLeftRule( _, Ant( 0 ), defAtom ) ).
          u( ImpRightRule( _, Ant( 0 ), Suc( 0 ) ) ).
          c( LogicalAxiom( phi ) ).
          u( ConversionRightRule( _, Suc( 0 ), defAtom ) ).
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
        val Right( p1 ) = solvePropositional( comp.disjunction +: comp.clause )
        val p2 = ForallLeftBlock( p1, aux, vars )

        val p3 = ConversionLeftRule( p2, aux, splAtom )
        p3
      case AvatarComponent( AvatarGroundComp( atom, _ ) ) => LogicalAxiom( atom )
      case AvatarComponent( comp @ AvatarNegNonGroundComp( splAtom, aux, vars, idx ) ) =>
        val Right( p1 ) = solvePropositional( comp.clause :+ comp.disjunction )
        val p2 = ForallRightBlock( p1, aux, vars )
        val p3 = ConversionRightRule( p2, aux, splAtom )
        p3
      case AvatarSplit( q, indices, AvatarGroundComp( _, _ ) ) => f( q )
      case p @ AvatarSplit( q, _, comp @ AvatarNonGroundComp( splAtom, aux, vars ) ) =>
        var p_ = f( q )
        for {
          a <- comp.clause.antecedent
          if p_.conclusion.antecedent contains a
        } p_ = NegRightRule( p_, a )
        def mkOr( lits: Formula ): Unit =
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
        p_ = ConversionRightRule( p_, aux, splAtom )
        p_

      case p @ DefIntro( q, i: Suc, definition, args ) =>
        ConversionRightRule( f( q ), q.conclusion( i ), p.defAtom )

      case p @ DefIntro( q, i: Ant, definition, args ) =>
        ConversionLeftRule( f( q ), q.conclusion( i ), p.defAtom )

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

      case p: AllL    => reducef( p )( f => ForallSkRightRule( LogicalAxiom( instantiate( f, p.skolemTerm ) ), Suc( 0 ), f, p.skolemTerm ) )
      case p: ExR     => reducef( p )( f => ExistsSkLeftRule( LogicalAxiom( instantiate( f, p.skolemTerm ) ), Ant( 0 ), f, p.skolemTerm ) )

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
  def reduceAxiom( proof: LKProof, idx: SequentIndex )( func: Formula => LKProof ): LKProof =
    new LKVisitor[Sequent[Boolean]] {
      val formula = proof.conclusion( idx )
      val proofToInsert = func( formula )
      val connToInsert = SequentConnector( proofToInsert.endSequent, formula +: Sequent() :+ formula,
        for ( i <- proofToInsert.endSequent.indicesSequent )
          yield if ( proofToInsert.endSequent( i ) == formula )
          Seq( if ( idx.isSuc ) Ant( 0 ) else Suc( 0 ) )
        else Seq() )

      val extraSequent =
        if ( idx.isSuc ) proofToInsert.conclusion.removeFromAntecedent( formula )
        else proofToInsert.conclusion.removeFromSuccedent( formula )
      val formulaMultiplicities = Map() ++ extraSequent.polarizedElements.groupBy( identity ).view.mapValues( _.size ).toMap

      override def transportToSubProof( isAncestor: Sequent[Boolean], proof: LKProof, subProofIdx: Int ) =
        proof.occConnectors( subProofIdx ).parent( isAncestor, false )

      override def visitLogicalAxiom( proof: LogicalAxiom, isAncestor: Sequent[Boolean] ) =
        isAncestor.find( _ == true ) match {
          case Some( i ) => ( proofToInsert, connToInsert )
          case None      => withIdentitySequentConnector( proof )
        }

      // Contract ancestors as soon as possible, and then skip the following contractions.
      override def recurse( proof: LKProof, isAncestor: Sequent[Boolean] ): ( LKProof, SequentConnector ) = {
        if ( isAncestor.forall( _ == false ) ) {
          ( proof, SequentConnector( proof.conclusion ) )
        } else {
          val mainAncestors = proof.mainIndices.filter( isAncestor( _ ) )
          if ( !proof.isInstanceOf[LogicalAxiom] && mainAncestors.nonEmpty ) {
            val mainAncestor = mainAncestors.head
            val ( proof3, conn ) = if ( mainAncestor.isAnt ) {
              val proof2 = CutRule( LogicalAxiom( proof.conclusion( mainAncestor ) ), Suc( 0 ), proof, mainAncestor )
              recurse( proof2, proof2.getRightSequentConnector.inv.parent( isAncestor, true ) )
            } else {
              val proof2 = CutRule( proof, mainAncestor, LogicalAxiom( proof.conclusion( mainAncestor ) ), Ant( 0 ) )
              recurse( proof2, proof2.getLeftSequentConnector.inv.parent( isAncestor, true ) )
            }
            // FIXME: do this properly
            val proof4 = cutNormal( proof3 )
            ( proof4, SequentConnector.guessInjection( toUpper = proof3.conclusion, fromLower = proof4.conclusion ) * conn )
          } else {
            val ( proofNew, conn ) = super.recurse( proof, isAncestor )
            contract( proofNew, conn )
          }
        }
      }
      def contract( subProof: LKProof, subConn: SequentConnector ): ( LKProof, SequentConnector ) = {
        val newIndices = subConn.parentsSequent.indicesWhere( _.isEmpty )
        val newIndicesByFormula = newIndices.groupBy( i => subProof.conclusion( i ) -> i.polarity )
        newIndicesByFormula.find( ni => ni._2.size > formulaMultiplicities( ni._1 ) ) match {
          case Some( ( _, indices ) ) =>
            val Seq( i, j, _* ) = indices
            val contracted = if ( i.isSuc ) ContractionRightRule( subProof, i, j ) else ContractionLeftRule( subProof, i, j )
            ( contracted, contracted.getSequentConnector * subConn )
          case None => ( subProof, subConn )
        }
      }
      override def visitContractionLeft( proof: ContractionLeftRule, isAncestor: Sequent[Boolean] ): ( LKProof, SequentConnector ) =
        one2one( proof, isAncestor ) {
          case Seq( ( subProof, subConn ) ) =>
            if ( subConn.children( proof.aux1 ).isEmpty ) return ( subProof, subConn )
            ContractionLeftRule( subProof, subConn child proof.aux1, subConn child proof.aux2 )
        }
      override def visitContractionRight( proof: ContractionRightRule, isAncestor: Sequent[Boolean] ): ( LKProof, SequentConnector ) =
        one2one( proof, isAncestor ) {
          case Seq( ( subProof, subConn ) ) =>
            if ( subConn.children( proof.aux1 ).isEmpty ) return ( subProof, subConn )
            ContractionRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 )
        }
    }.apply( proof, proof.conclusion.indicesSequent.map( _ == idx ) )

  /** Proof of t=s :- s=t */
  def mkSymmProof( t: Expr, s: Expr ): LKProof =
    ProofBuilder.
      c( ReflexivityAxiom( t ) ).
      u( WeakeningLeftRule( _, Eq( t, s ) ) ).
      u( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Eq( s, t ) ) ).
      qed
}
