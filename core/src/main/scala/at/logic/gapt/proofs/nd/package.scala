package at.logic.gapt.proofs

import at.logic.gapt.expr._

package object nd {

  implicit val ndSubstitutable: ClosedUnderSub[NDProof] = ( s, p ) => p match {
    case ContractionRule( q, a1, a2 ) => ContractionRule( s( q ), a1, a2 )
    case LogicalAxiom( f )            => LogicalAxiom( s( f ) )
    case TheoryAxiom( f )             => TheoryAxiom( s( f ) )

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

    case TopIntroRule()             => TopIntroRule()
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
    case ForallElimRule( q, _, t, _ )      => ForallElimRule( s( q ), s( t ) )

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

}
