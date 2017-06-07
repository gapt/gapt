package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.SkolemFunctions
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofWithCut }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution.ResolutionProof

trait Checkable[-T] {
  def check( context: Context, obj: T ): Unit
}
object Checkable {
  implicit object contextElementIsCheckable extends Checkable[Context.Update] {
    def check( context: Context, elem: Context.Update ): Unit = elem( context )
  }

  implicit object typeIsCheckable extends Checkable[Ty] {
    override def check( context: Context, ty: Ty ): Unit =
      ty match {
        case ty @ TBase( name, params ) =>
          require(
            context.isType( ty ),
            s"Unknown base type: $name"
          )
          params.foreach( check( context, _ ) )
        case TVar( _ ) =>
        case in -> out =>
          check( context, in )
          check( context, out )
      }
  }

  implicit object expressionIsCheckable extends Checkable[Expr] {
    def check( context: Context, expr: Expr ): Unit =
      expr match {
        case c @ Const( name, _ ) =>
          require(
            context.constant( name ).exists( defC => syntacticMatching( defC, c ).isDefined ),
            s"Unknown constant: $c"
          )
        case Var( _, t ) => context.check( t )
        case Abs( v, e ) =>
          check( context, v )
          check( context, e )
        case App( a, b ) =>
          check( context, a )
          check( context, b )
      }
  }

  implicit def sequentIsCheckable[T: Checkable] = new Checkable[Sequent[T]] {
    def check( context: Context, sequent: Sequent[T] ) =
      sequent.foreach( context.check( _ ) )
  }

  implicit object lkIsCheckable extends Checkable[LKProof] {
    import at.logic.gapt.proofs.lk._

    def check( context: Context, p: LKProof ): Unit = {
      // make sure the end-sequent does not contain Skolem functions
      context.check( p.endSequent )

      var ctx = context

      val skolemFunctions = SkolemFunctions( p.subProofs.collect {
        case sk: SkolemQuantifierRule =>
          sk.skolemConst -> sk.skolemDef
      } )
      skolemFunctions.orderedDefinitions.reverse.
        map( Context.SkolemFun.tupled ).foreach( ctx += _ )

      for ( q <- p.subProofs )
        ctx.check( q.endSequent )

      // TODO: definition rules need to be improved to support checking

      p.subProofs.foreach {
        case ForallLeftRule( _, _, a, t, v )  => ctx.check( t )
        case ExistsRightRule( _, _, a, t, v ) => ctx.check( t )
        case q: EqualityRule                  =>
        case q @ InductionRule( cases, formula, term ) =>
          ctx.check( formula )
          ctx.check( term )
          val Some( ctrs ) = ctx.getConstructors( q.indTy.asInstanceOf[TBase] )
          require( q.cases.map( _.constructor ) == ctrs )
        case sk: SkolemQuantifierRule =>
          require( ctx.skolemDef( sk.skolemConst ).contains( sk.skolemDef ) )
          ctx.check( sk.skolemTerm )
        case StrongQuantifierRule( _, _, _, _, _ ) =>
        case _: ReflexivityAxiom | _: LogicalAxiom =>
        case ProofLink( name, sequent ) =>
          val declSeq = ctx.get[Context.ProofNames].lookup( name )
          require( declSeq.nonEmpty, s"Proof name $name does not exist in context" )
          require( declSeq.get isSubsetOf sequent, s"$declSeq\nis not a subsequent of\n$sequent" )
        case TopAxiom | BottomAxiom
          | _: NegLeftRule | _: NegRightRule
          | _: AndLeftRule | _: AndRightRule
          | _: OrLeftRule | _: OrRightRule
          | _: ImpLeftRule | _: ImpRightRule =>
        case _: ContractionRule | _: WeakeningLeftRule | _: WeakeningRightRule =>
        case _: CutRule =>
        case d: DefinitionRule =>
          require(
            ctx.isDefEq( d.mainFormula, d.auxFormula ),
            s"${ctx.normalize( d.mainFormula )} != ${ctx.normalize( d.auxFormula )}"
          )
      }
    }
  }

  implicit object expansionProofIsCheckable extends Checkable[ExpansionProof] {
    import at.logic.gapt.proofs.expansion._

    def check( context: Context, ep: ExpansionProof ): Unit = {
      context.check( ep.shallow )

      var ctx = context
      ep.skolemFunctions.orderedDefinitions.map( Context.SkolemFun.tupled ).foreach( ctx += _ )

      ep.subProofs.foreach {
        case ETTop( _ ) | ETBottom( _ ) | ETNeg( _ ) | ETAnd( _, _ ) | ETOr( _, _ ) | ETImp( _, _ ) =>
        case ETWeakening( _, _ ) | ETAtom( _, _ ) =>
        case ETWeakQuantifier( _, insts ) =>
          insts.keys.foreach( ctx.check( _ ) )
        case ETStrongQuantifier( _, _, _ ) =>
        case sk @ ETSkolemQuantifier( _, skT, skD, _ ) =>
          require( ctx.skolemDef( sk.skolemConst ).contains( skD ) )
          ctx.check( skT )
        case ETDefinition( sh, child ) =>
          require(
            ctx.isDefEq( sh, child.shallow ),
            s"${ctx.normalize( sh )} != ${ctx.normalize( child.shallow )}"
          )
      }
    }
  }

  implicit object expansionProofWithCutIsCheckable extends Checkable[ExpansionProofWithCut] {
    def check( context: Context, epwc: ExpansionProofWithCut ): Unit =
      context.check( epwc.expansionWithCutAxiom )
  }

  implicit object resolutionIsCheckable extends Checkable[ResolutionProof] {
    import at.logic.gapt.proofs.resolution._

    def check( context0: Context, p: ResolutionProof ) = {
      var ctx = context0

      p.skolemFunctions.orderedDefinitions.map( Context.SkolemFun.tupled ).foreach( ctx += _ )

      for ( Defn( defConst, defn ) <- p.subProofs )
        ctx += ( defConst.name, defn )

      p.subProofs.collect {
        case AvatarComponent( defn )   => defn
        case AvatarSplit( _, _, defn ) => defn
      }.flatMap {
        case AvatarNonGroundComp( Const( name, _ ), defn, _ )       => Some( name -> defn )
        case AvatarNegNonGroundComp( Const( name, _ ), defn, _, _ ) => Some( name -> defn )
        case AvatarGroundComp( _, _ )                               => None
      }.foreach {
        case ( name, defn ) => ctx += ( name, defn )
      }

      p.subProofs.foreach {
        case Input( sequent )           => context0.check( sequent )
        case Refl( term )               => ctx.check( term )
        case Taut( form )               => ctx.check( form )
        case Defn( _, _ )               => // already checked
        case _: WeakQuantResolutionRule =>
        case q: SkolemQuantResolutionRule =>
          require( ctx.skolemDef( q.skolemConst ).contains( q.skolemDef ) )
          ctx.check( q.skolemTerm )
        case q @ DefIntro( _, _, definition, _ ) =>
          require( ctx.contains( definition ) )
        case _: PropositionalResolutionRule =>
        case _: AvatarComponent | _: AvatarSplit | _: AvatarContradiction =>
        case _: Flip | _: Paramod =>
        case _: Resolution =>
        case _: Factor =>
        case _: Subst =>
      }
    }
  }
}
