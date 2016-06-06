package at.logic.gapt.proofs

import at.logic.gapt.expr._

import scala.collection.mutable

package object resolution {
  implicit object resolutionProofsAreReplaceable extends ClosedUnderReplacement[ResolutionProof] {
    def replace( component: AvatarComponent, repl: PartialFunction[LambdaExpression, LambdaExpression] ): AvatarComponent = component match {
      case AvatarGroundComp( atom, pol )           => AvatarGroundComp( TermReplacement( atom, repl ), pol )
      case AvatarNonGroundComp( atom, defn, vars ) => AvatarNonGroundComp( TermReplacement( atom, repl ), TermReplacement( defn, repl ), vars )
      case AvatarNegNonGroundComp( atom, defn, vars, idx ) =>
        AvatarNegNonGroundComp( TermReplacement( atom, repl ), TermReplacement( defn, repl ), vars, idx )
    }
    def replace( subst: Substitution, repl: PartialFunction[LambdaExpression, LambdaExpression] ): Substitution =
      Substitution( subst.map.map { case ( f, t ) => f -> TermReplacement( t, repl ) } )

    def replace( proof: ResolutionProof, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ResolutionProof = {
      val memo = mutable.Map[ResolutionProof, ResolutionProof]()

      def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
        case Input( sequent )             => Input( TermReplacement( sequent, repl ) )
        case Refl( term )                 => Refl( TermReplacement( term, repl ) )
        case Taut( formula )              => Taut( TermReplacement( formula, repl ) )
        case Factor( q, i1, i2 )          => Factor( f( q ), i1, i2 )
        case Subst( q, subst )            => Subst( f( q ), replace( subst, repl ) )
        case Resolution( q1, l1, q2, l2 ) => Resolution( f( q1 ), l1, f( q2 ), l2 )
        case Paramod( q1, l1, dir, q2, l2, con ) =>
          val q1New = f( q1 )
          val q2New = f( q2 )
          val ( equation, auxFormula ) = ( q1New.conclusion( l1 ), q2New.conclusion( l2 ) )
          val Abs( v, subContext ) = con
          val v_ = rename( v, freeVariables( equation ) ++ freeVariables( auxFormula ) )
          val contextNew = Abs( v_, TermReplacement( Substitution( v, v_ )( subContext ), repl ) )
          Paramod( q1New, l1, dir, q2New, l2, contextNew )
        case AvatarSplit( q, components ) =>
          AvatarSplit( f( q ), components map { replace( _, repl ) } )
        case AvatarAbsurd( q )                 => AvatarAbsurd( f( q ) )
        case AvatarComponentIntro( component ) => AvatarComponentIntro( replace( component, repl ) )
        case DefIntro( q, i, defAtom, definition ) =>
          DefIntro( f( q ), i, TermReplacement( defAtom, repl ), TermReplacement( definition, repl ) )
        case TopL( q, i )                => TopL( f( q ), i )
        case BottomR( q, i )             => BottomR( f( q ), i )
        case NegL( q, i )                => NegL( f( q ), i )
        case NegR( q, i )                => NegR( f( q ), i )
        case AndL( q, i )                => AndL( f( q ), i )
        case OrR( q, i )                 => OrR( f( q ), i )
        case ImpR( q, i )                => ImpR( f( q ), i )
        case AndR1( q, i )               => AndR1( f( q ), i )
        case OrL1( q, i )                => OrL1( f( q ), i )
        case ImpL1( q, i )               => ImpL1( f( q ), i )
        case AndR2( q, i )               => AndR2( f( q ), i )
        case OrL2( q, i )                => OrL2( f( q ), i )
        case ImpL2( q, i )               => ImpL2( f( q ), i )
        case AllL( q, i, skTerm, skDef ) => AllL( f( q ), i, TermReplacement( skTerm, repl ), TermReplacement( skDef, repl ) )
        case ExR( q, i, skTerm, skDef )  => ExR( f( q ), i, TermReplacement( skTerm, repl ), TermReplacement( skDef, repl ) )
        case AllR( q, i, v )             => AllR( f( q ), i, TermReplacement( v, repl ).asInstanceOf[Var] )
        case ExL( q, i, v )              => ExL( f( q ), i, TermReplacement( v, repl ).asInstanceOf[Var] )
      } )

      f( proof )
    }
  }
}
