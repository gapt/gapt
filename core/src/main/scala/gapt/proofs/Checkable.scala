package gapt.proofs

import gapt.expr._
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution.ResolutionProof

import scala.collection.mutable

trait Checkable[-T] {
  def check( obj: T )( implicit ctx: Context ): Unit
}
object Checkable {
  def requireDefEq( a: Expr, b: Expr )( implicit ctx: Context ): Unit =
    require( ctx.isDefEq( a, b ), s"${ctx.normalize( a ).toSigRelativeString} != ${ctx.normalize( b ).toSigRelativeString}" )

  implicit object contextElementIsCheckable extends Checkable[Context.Update] {
    def check( elem: Context.Update )( implicit context: Context ): Unit = elem( context )
  }

  class ExpressionChecker( implicit ctx: Context ) {
    private val validTy = mutable.Set[Ty]()
    def check( ty: Ty ): Unit = {
      if ( validTy.contains( ty ) ) return
      ty match {
        case ty @ TBase( name, params ) =>
          require(
            ctx.isType( ty ),
            s"Unknown base type: $name" )
          params.foreach( check )
        case TVar( _ ) =>
        case in ->: out =>
          check( in )
          check( out )
      }
      validTy += ty
    }

    private val validExpr = mutable.Set[Expr]()
    def check( expr: Expr ): Unit = {
      if ( validExpr( expr ) ) return
      expr match {
        case c @ Const( name, _, params ) =>
          require( ctx.constant( name, params ).contains( c ), s"Unknown constant: $c" )
        case Var( _, t ) =>
          check( t )
        case Abs( v, e ) =>
          check( v )
          check( e )
        case App( a, b ) =>
          check( a )
          check( b )
      }
      validExpr += expr
    }
  }

  implicit object typeIsCheckable extends Checkable[Ty] {
    override def check( ty: Ty )( implicit context: Context ): Unit =
      new ExpressionChecker().check( ty )
  }

  implicit object expressionIsCheckable extends Checkable[Expr] {
    def check( expr: Expr )( implicit context: Context ): Unit =
      new ExpressionChecker().check( expr )
  }

  implicit def sequentIsCheckable[T: Checkable] = new Checkable[Sequent[T]] {
    def check( sequent: Sequent[T] )( implicit context: Context ) =
      sequent.foreach( context.check( _ ) )
  }

  implicit object lkIsCheckable extends Checkable[LKProof] {
    import gapt.proofs.lk._

    def check( p: LKProof )( implicit ctx: Context ): Unit = {
      ctx.check( p.endSequent )
      p.subProofs.foreach {
        case ForallLeftRule( _, _, a, t, v )  => ctx.check( t )
        case ExistsRightRule( _, _, a, t, v ) => ctx.check( t )
        case q: EqualityRule =>
          ctx.check( q.replacementContext )
        case q @ InductionRule( cases, formula, term ) =>
          ctx.check( formula )
          ctx.check( term )
          val Some( ctrsInCtx ) = ctx.getConstructors( q.indTy.asInstanceOf[TBase] )
          val ctrsInProof = cases.map( _.constructor )
          require(
            ctrsInProof == ctrsInCtx,
            s"Induction rule has incorrect constructors: ${ctrsInProof.mkString( ", " )}\n" +
              s"Expected: ${ctrsInCtx.mkString( ", " )}" )
        case sk: SkolemQuantifierRule =>
          require( ctx.skolemDef( sk.skolemConst ).contains( sk.skolemDef ) )
          ctx.check( sk.skolemTerm )
        case StrongQuantifierRule( _, _, _, _, _ ) =>
        case _: ReflexivityAxiom | _: LogicalAxiom =>
        case ProofLink( name, sequent ) =>
          val declSeq = ctx.get[Context.ProofNames].lookup( name )
          require( declSeq.nonEmpty, s"Proof name $name does not exist in context" )
          require( declSeq.get == sequent, s"$declSeq\nis not equal to \n$sequent" )
        case TopAxiom | BottomAxiom
          | _: NegLeftRule | _: NegRightRule
          | _: AndLeftRule | _: AndRightRule
          | _: OrLeftRule | _: OrRightRule
          | _: ImpLeftRule | _: ImpRightRule =>
        case _: ContractionRule | _: WeakeningLeftRule | _: WeakeningRightRule =>
        case _: CutRule =>
        case d: DefinitionRule =>
          requireDefEq( d.mainFormula, d.auxFormula )( ctx )
      }
    }
  }

  implicit object expansionProofIsCheckable extends Checkable[ExpansionProof] {
    import gapt.proofs.expansion._

    def check( ep: ExpansionProof )( implicit ctx: Context ): Unit = {
      ctx.check( ep.shallow )
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
          requireDefEq( sh, child.shallow )( ctx )
        case ETMerge( _, _ ) =>
      }
    }
  }

  implicit object resolutionIsCheckable extends Checkable[ResolutionProof] {
    import gapt.proofs.resolution._

    def check( p: ResolutionProof )( implicit ctx: Context ): Unit = {
      def checkAvatarDef( comp: AvatarDefinition ): Unit =
        for ( ( df, by ) <- comp.inducedDefinitions )
          requireDefEq( df, by )( ctx )

      p.subProofs.foreach {
        case Input( sequent )           => ctx.check( sequent )
        case Refl( term )               => ctx.check( term )
        case Taut( form )               => ctx.check( form )
        case Defn( df, by )             => require( ctx.isDefEq( df, by ) )
        case _: WeakQuantResolutionRule =>
        case q: SkolemQuantResolutionRule =>
          require( ctx.skolemDef( q.skolemConst ).contains( q.skolemDef ) )
          ctx.check( q.skolemTerm )
        case DefIntro( _, _, definition, _ ) =>
          requireDefEq( definition.what, definition.by )( ctx )
        case _: PropositionalResolutionRule =>
        case AvatarComponent( defn ) => checkAvatarDef( defn )
        case AvatarSplit( _, _, defn ) => checkAvatarDef( defn )
        case _: AvatarComponent | _: AvatarSplit | _: AvatarContradiction =>
        case _: Flip | _: Paramod =>
        case _: Resolution =>
        case _: Factor =>
        case _: Subst =>
      }
    }
  }
}
