package gapt.proofs

import gapt.expr._

import scala.collection.mutable

package object resolution {
  implicit object avatarComponentsAreReplaceable extends ClosedUnderReplacement[AvatarDefinition] {
    def replace( component: AvatarDefinition, repl: PartialFunction[Expr, Expr] ): AvatarDefinition = component match {
      case AvatarGroundComp( atom, pol )           => AvatarGroundComp( TermReplacement( atom, repl ), pol )
      case AvatarNonGroundComp( atom, defn, vars ) => AvatarNonGroundComp( TermReplacement( atom, repl ), TermReplacement( defn, repl ), vars )
      case AvatarNegNonGroundComp( atom, defn, vars, idx ) =>
        AvatarNegNonGroundComp( TermReplacement( atom, repl ), TermReplacement( defn, repl ), vars, idx )
    }
    def names( component: AvatarDefinition ) = component match {
      case AvatarGroundComp( atom, _ ) => containedNames( atom )
      case AvatarNonGroundComp( atom, defn, vars ) =>
        containedNames( atom ) ++ containedNames( defn ) ++ containedNames( vars )
      case AvatarNegNonGroundComp( atom, defn, vars, _ ) =>
        containedNames( atom ) ++ containedNames( defn ) ++ containedNames( vars )
    }
  }

  implicit object resolutionProofsAreReplaceable extends ClosedUnderReplacement[ResolutionProof] {
    def replace( proof: ResolutionProof, repl: PartialFunction[Expr, Expr] ): ResolutionProof = {
      val memo = mutable.Map[ResolutionProof, ResolutionProof]()

      def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
        case Input( sequent )             => Input( TermReplacement( sequent, repl ) map BetaReduction.betaNormalize )
        case Refl( term )                 => Refl( BetaReduction betaNormalize TermReplacement( term, repl ) )
        case Taut( formula )              => Taut( BetaReduction betaNormalize TermReplacement( formula, repl ) )
        case Defn( defConst, definition ) => Defn( TermReplacement( defConst, repl ).asInstanceOf[HOLAtomConst], TermReplacement( definition, repl ) )
        case Factor( q, i1, i2 )          => Factor( f( q ), i1, i2 )
        case Subst( q, subst )            => Subst( f( q ), TermReplacement( subst, repl ) )
        case Resolution( q1, l1, q2, l2 ) => Resolution( f( q1 ), l1, f( q2 ), l2 )
        case Paramod( q1, l1, dir, q2, l2, con ) =>
          val q1New = f( q1 )
          val q2New = f( q2 )
          val ( equation, auxFormula ) = ( q1New.conclusion( l1 ), q2New.conclusion( l2 ) )
          val Abs( v, subContext ) = con
          val v_ = rename( v, freeVariables( equation ) ++ freeVariables( auxFormula ) )
          val contextNew = TermReplacement( Abs( v_, Substitution( v, v_ )( subContext ) ), repl )
          Paramod( q1New, l1, dir, q2New, l2, contextNew )
        case AvatarSplit( q, indices, component ) =>
          AvatarSplit( f( q ), indices, TermReplacement( component, repl ) )
        case AvatarContradiction( q )     => AvatarContradiction( f( q ) )
        case AvatarComponent( component ) => AvatarComponent( TermReplacement( component, repl ) )
        case p @ DefIntro( q, i, definition, args ) =>
          val Definition( what, by ) = definition
          val definitionNew = Definition( TermReplacement( what, repl ).asInstanceOf[Const], TermReplacement( by, repl ) )
          val argsNew = TermReplacement( args, repl )
          DefIntro( f( q ), i, definitionNew, argsNew )
        case Flip( q, i )                => Flip( f( q ), i )
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

    def names( proof: ResolutionProof ) = {
      val ns = Set.newBuilder[VarOrConst]
      for ( p <- proof.subProofs ) {
        ns ++= containedNames( p.conclusion )
        ns ++= containedNames( p.assertions )
        p match {
          case AvatarComponent( comp ) =>
            ns ++= containedNames( comp )
          case AvatarSplit( _, _, comp ) =>
            ns ++= containedNames( comp )
          case Subst( _, subst ) =>
            ns ++= containedNames( subst )
          case DefIntro( _, _, definition, repContext ) =>
            val Definition( what, by ) = definition
            ns ++= containedNames( what )
            ns ++= containedNames( by )
          case Defn( defConst, definition ) =>
            ns += defConst
            ns ++= containedNames( definition )
          case p: SkolemQuantResolutionRule =>
            ns ++= containedNames( p.skolemTerm )
            ns ++= containedNames( p.skolemDef )
          case p: WeakQuantResolutionRule =>
            ns ++= containedNames( p.variable )
          case _ =>
        }
      }
      ns.result()
    }
  }
}
