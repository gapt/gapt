package gapt.proofs

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.rename

package object nd {

  implicit val ndSubstitutable: ClosedUnderSub[NDProof] = ( s, p ) => p match {
    case ContractionRule( q, a1, a2 ) => ContractionRule( s( q ), a1, a2 )
    case LogicalAxiom( f )            => LogicalAxiom( s( f ) )
    case TheoryAxiom( f )             => TheoryAxiom( s( f ) )
    case WeakeningRule( q, f )        => WeakeningRule( s( q ), s( f ) )

    case AndElim1Rule( q )            => AndElim1Rule( s( q ) )
    case AndElim2Rule( q )            => AndElim2Rule( s( q ) )
    case AndIntroRule( q1, q2 )       => AndIntroRule( s( q1 ), s( q2 ) )

    case OrElimRule( maj, min1, a1, min2, a2 ) =>
      OrElimRule( s( maj ), s( min1 ), a1, s( min2 ), a2 )
    case OrIntro1Rule( q, f )       => OrIntro1Rule( s( q ), s( f ) )
    case OrIntro2Rule( q, f )       => OrIntro2Rule( s( q ), s( f ) )

    case NegElimRule( maj, min )    => NegElimRule( s( maj ), s( min ) )
    case NegIntroRule( q, a )       => NegIntroRule( s( q ), a )

    case ImpElimRule( maj, min )    => ImpElimRule( s( maj ), s( min ) )
    case ImpIntroRule( q, a )       => ImpIntroRule( s( q ), a )

    case TopIntroRule               => TopIntroRule
    case BottomElimRule( maj, min ) => BottomElimRule( s( maj ), s( min ) )

    case EqualityIntroRule( t )     => EqualityIntroRule( s( t ) )
    case EqualityElimRule( maj, min, f, x ) =>
      val Abs( x_, f_ ) = s( Abs( x, f ) )
      EqualityElimRule( s( maj ), s( min ), f_.asInstanceOf[Formula], x_ )

    case ExcludedMiddleRule( c1, a1, c2, a2 ) => ExcludedMiddleRule( s( c1 ), a1, s( c2 ), a2 )

    case ForallIntroRule( q, ev, qv ) if s.range.contains( ev ) =>
      val ev_ = rename( ev, freeVariables( p.conclusion ) ++ s.range + qv )
      s( ForallIntroRule( Substitution( ev -> ev_ )( q ), ev_, qv ) )
    case p @ ForallIntroRule( q, ev, _ ) if !s.range.contains( ev ) =>
      ForallIntroRule( Substitution( s.map - ev )( q ), s( p.mainFormula ), ev )
    case ForallElimRule( q, t )            => ForallElimRule( s( q ), s( t ) )

    case p @ ExistsIntroRule( q, _, t, _ ) => ExistsIntroRule( s( q ), s( p.mainFormula ), s( t ) )
    case ExistsElimRule( maj, min, a, ev ) if s.range.contains( ev ) =>
      val ev_ = rename( ev, freeVariables( min.conclusion ) ++ s.range )
      s( ExistsElimRule( maj, Substitution( ev -> ev_ )( min ), a, ev_ ) )
    case ExistsElimRule( maj, min, a, ev ) if !s.range.contains( ev ) =>
      ExistsElimRule( s( maj ), Substitution( s.map - ev )( min ), a, ev )

    case p @ InductionRule( cases, f, t ) if s.range.intersect( p.eigenVariables ).nonEmpty =>
      val renaming = rename( p.cases.flatMap( _.eigenVars ), freeVariables( p.conclusion ) ++ s.range )
      val rs = Substitution( renaming )
      s( InductionRule( cases.map { case InductionCase( q, c, h, evs ) => InductionCase( rs( q ), c, h, evs.map( renaming ) ) }, f, t ) )
    case p @ InductionRule( cases, f, t ) if s.range.intersect( p.eigenVariables ).isEmpty =>
      val s_ = Substitution( s.map -- p.eigenVariables )
      InductionRule( cases.map( c => c.copy( proof = s_( c.proof ) ) ), s( f ).asInstanceOf[Abs], s( t ) )
  }

  implicit object casesReplaceable extends ClosedUnderReplacement[InductionCase] {
    private implicit def ndReplaceable: ClosedUnderReplacement[NDProof] = replaceable

    override def replace( c: InductionCase, p: PartialFunction[Expr, Expr] ): InductionCase =
      InductionCase( TermReplacement( c.proof, p ), TermReplacement( c.constructor, p ).asInstanceOf[Const],
        c.hypotheses, TermReplacement( c.eigenVars, p ).map( _.asInstanceOf[Var] ) )

    override def names( c: InductionCase ): Set[VarOrConst] =
      containedNames( c.proof ) + c.constructor ++ c.eigenVars
  }

  implicit object replaceable extends ClosedUnderReplacement[NDProof] {
    def replace( p: NDProof, r: PartialFunction[Expr, Expr] ): NDProof = p match {
      case ContractionRule( q, a1, a2 ) => ContractionRule( replace( q, r ), a1, a2 )
      case LogicalAxiom( f )            => LogicalAxiom( TermReplacement( f, r ) )
      case TheoryAxiom( f )             => TheoryAxiom( TermReplacement( f, r ) )

      case AndElim1Rule( q )            => AndElim1Rule( replace( q, r ) )
      case AndElim2Rule( q )            => AndElim2Rule( replace( q, r ) )
      case AndIntroRule( q1, q2 )       => AndIntroRule( replace( q1, r ), replace( q2, r ) )

      case OrElimRule( maj, min1, a1, min2, a2 ) =>
        OrElimRule( replace( maj, r ), replace( min1, r ), a1, replace( min2, r ), a2 )
      case OrIntro1Rule( q, f ) =>
        OrIntro1Rule( replace( q, r ), TermReplacement( f, r ) )
      case OrIntro2Rule( q, f ) =>
        OrIntro2Rule( replace( q, r ), TermReplacement( f, r ) )

      case NegElimRule( maj, min ) =>
        NegElimRule( replace( maj, r ), replace( min, r ) )
      case NegIntroRule( q, a ) =>
        NegIntroRule( replace( q, r ), a )

      case ImpElimRule( maj, min ) =>
        ImpElimRule( replace( maj, r ), replace( min, r ) )
      case ImpIntroRule( q, a ) =>
        ImpIntroRule( replace( q, r ), a )

      case TopIntroRule               => TopIntroRule
      case BottomElimRule( maj, min ) => BottomElimRule( replace( maj, r ), TermReplacement( min, r ) )

      case EqualityIntroRule( t )     => EqualityIntroRule( TermReplacement( t, r ) )
      case EqualityElimRule( maj, min, f, x ) =>
        EqualityElimRule( replace( maj, r ), replace( min, r ), TermReplacement( f, r ), TermReplacement( x, r ).asInstanceOf[Var] )

      case ExcludedMiddleRule( c1, a1, c2, a2 ) =>
        ExcludedMiddleRule( replace( c1, r ), a1, replace( c2, r ), a2 )

      case ForallIntroRule( q, ev, qv ) =>
        ForallIntroRule( replace( q, r ), TermReplacement( ev, r ).asInstanceOf[Var],
          TermReplacement( qv, r ).asInstanceOf[Var] )
      case ForallElimRule( q, t ) =>
        ForallElimRule( replace( q, r ), TermReplacement( t, r ) )

      case ExistsIntroRule( q, a, t, v ) =>
        ExistsIntroRule( replace( q, r ), TermReplacement( a, r ), TermReplacement( t, r ), TermReplacement( v, r ).asInstanceOf[Var] )
      case ExistsElimRule( maj, min, a, ev ) =>
        ExistsElimRule( replace( maj, r ), replace( min, r ), a, TermReplacement( ev, r ).asInstanceOf[Var] )

      case InductionRule( cases, f, t ) =>
        InductionRule( TermReplacement( cases, r ), TermReplacement( f, r ).asInstanceOf[Abs], TermReplacement( t, r ) )
    }

    def names( p: NDProof ): Set[VarOrConst] = p match {
      case ContractionRule( q, a1, a2 )          => names( q )
      case LogicalAxiom( f )                     => containedNames( f )
      case TheoryAxiom( f )                      => containedNames( f )

      case AndElim1Rule( q )                     => names( q )
      case AndElim2Rule( q )                     => names( q )
      case AndIntroRule( q1, q2 )                => names( q1 ).union( names( q2 ) )

      case OrElimRule( maj, min1, a1, min2, a2 ) => names( maj ) union names( min1 ) union names( min2 )
      case OrIntro1Rule( q, f )                  => names( q )
      case OrIntro2Rule( q, f )                  => names( q )

      case NegElimRule( maj, min )               => names( maj ) union names( min )
      case NegIntroRule( q, a )                  => names( q )

      case ImpElimRule( maj, min )               => names( maj ) union names( min )
      case ImpIntroRule( q, a )                  => names( q )

      case TopIntroRule                          => Set.empty
      case BottomElimRule( maj, min )            => names( maj ) union containedNames( min )

      case EqualityIntroRule( t )                => containedNames( t )
      case EqualityElimRule( maj, min, f, x )    => names( maj ) union names( min )

      case ExcludedMiddleRule( c1, a1, c2, a2 )  => names( c1 ) union names( c2 )

      case ForallIntroRule( q, ev, qv )          => names( q ) + ev + qv
      case ForallElimRule( q, t )                => names( q ) union containedNames( t )

      case ExistsIntroRule( q, a, t, v )         => names( q ) union containedNames( a ) union containedNames( t ) + v
      case ExistsElimRule( maj, min, a, ev )     => names( maj ) union names( min ) + ev

      case InductionRule( cases, f, t )          => containedNames( cases ) union containedNames( f ) union containedNames( t )
    }
  }

}
