package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.ExpansionProofToLK
import at.logic.gapt.proofs.lk._

import scala.collection.mutable
import scalaz.\/-

object ResolutionToLKProof {

  def apply( proof: ResolutionProof ): LKProof =
    apply( proof, in => in.sequent match {
      case Sequent( Seq(), Seq( f ) ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case Sequent( Seq( f ), Seq() ) if freeVariables( f ).isEmpty => LogicalAxiom( f )
      case seq =>
        val fvs = freeVariables( seq ).toSeq
        ( solvePropositional( seq.toDisjunction +: seq ): @unchecked ) match {
          case \/-( proj ) =>
            ForallLeftBlock( proj, All.Block( fvs, seq.toDisjunction ), fvs )
        }
    } )

  def asDerivation( proof: ResolutionProof ): LKProof =
    apply( proof, in => TheoryAxiom( in.sequent.map( _.asInstanceOf[HOLAtom] ) ) )

  def apply( proof: ResolutionProof, input: Input => LKProof ): LKProof = {
    val memo = mutable.Map[ResolutionProof, LKProof]()

    def contract( p: ResolutionProof, q: LKProof ) =
      ContractionMacroRule( q, ( ( p.conclusion ++ p.assertions ) diff q.endSequent.distinct ) ++ q.endSequent.distinct )

    def f( p: ResolutionProof ): LKProof = memo.getOrElseUpdate( p, contract( p, p match {
      case in: Input       => input( in )
      case Taut( formula ) => LogicalAxiom( formula )
      case Refl( term )    => ReflexivityAxiom( term )

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

      case p @ AvatarAbsurd( q ) => f( q )
      case AvatarComponentIntro( comp @ AvatarNonGroundComp( splAtom, definition, vars ) ) =>
        val \/-( p1 ) = solvePropositional( comp.disjunction +: comp.clause )
        val p2 = ForallLeftBlock( p1, definition, vars )
        val p3 = DefinitionLeftRule( p2, definition, splAtom )
        p3
      case AvatarComponentIntro( AvatarGroundComp( atom, _ ) )         => LogicalAxiom( atom )
      case AvatarComponentIntro( comp: AvatarNegNonGroundComp )        => LogicalAxiom( comp.propAtom )
      case AvatarComponentElim( q, indices, AvatarGroundComp( _, _ ) ) => f( q )
      case p @ AvatarComponentElim( q, _, comp @ AvatarNonGroundComp( splAtom, definition, vars ) ) =>
        var p_ = f( q )
        val pOrig = p_
        for ( a <- comp.clause.antecedent ) p_ = NegRightRule( p_, a )
        def mkOr( lits: HOLFormula ): Unit =
          lits match {
            case Or( lits_, lit ) =>
              mkOr( lits_ )
              p_ = OrRightMacroRule( p_, lits_, lit )
            case _ =>
          }
        mkOr( comp.disjunction )
        p_ = ForallRightBlock( p_, definition, vars )
        p_ = DefinitionRightRule( p_, definition, splAtom )
        p_

      // FIXME: add axiom reduction as in LKsk
      case _ =>
        val expansion = ResolutionToExpansionProof.withDefs( p )
        val \/-( lk ) = ExpansionProofToLK( expansion )
        lk
    } ) )

    f( proof )
  }

}
