package at.logic.gapt.expr

trait MatchingAlgorithm {
  def apply(
    pairs:             List[( Expr, Expr )],
    alreadyFixedSubst: PreSubstitution
  ): Traversable[Substitution]
}

object syntacticMatching extends syntacticMatching {
  def apply( from: FOLExpression, to: FOLExpression ): Option[FOLSubstitution] =
    apply( List( from -> to ) )

  def apply( pairs: List[( FOLExpression, FOLExpression )] )( implicit dummyImplicit: DummyImplicit ): Option[FOLSubstitution] =
    apply( pairs, Map[FOLVar, FOLTerm]() )

  def apply(
    pairs:             List[( FOLExpression, FOLExpression )],
    alreadyFixedSubst: Map[FOLVar, FOLTerm]
  )( implicit dummyImplicit: DummyImplicit ): Option[FOLSubstitution] =
    apply(
      pairs: List[( Expr, Expr )],
      Substitution( alreadyFixedSubst )
    ) map { _.asFOLSubstitution } headOption

  def apply( from: Expr, to: Expr ): Option[Substitution] =
    apply( List( from -> to ) )

  def apply( pairs: List[( Expr, Expr )] ): Option[Substitution] =
    apply( pairs, PreSubstitution() ).headOption

  def apply( a: Ty, b: Ty ): Option[Substitution] =
    apply( Nil, List( ( a, b ) ), PreSubstitution() ).headOption
}
class syntacticMatching extends MatchingAlgorithm {
  def apply(
    pairs:             List[( Expr, Expr )],
    alreadyFixedSubst: PreSubstitution
  ): Traversable[Substitution] = apply( pairs, Nil, alreadyFixedSubst )

  // TODO: rewrite using StateT[PreSubstitution, OptionT[X]]

  /**
   * Recursively looks for a Substitution σ such that for each (a, b) ∈ pairs, σ(a) = b.
   *
   * @param pairs A list of pairs of expressions.
   * @param alreadyFixedSubst The partial substitution which is already fixed, and can no longer be changed.
   * @return
   */
  def apply(
    pairs:             List[( Expr, Expr )],
    tyPairs:           List[( Ty, Ty )],
    alreadyFixedSubst: PreSubstitution
  ): Traversable[Substitution] = ( pairs, tyPairs ) match {
    case ( Nil, Nil ) => alreadyFixedSubst.toSubstitution :: Nil
    case ( _, first :: rest ) =>
      first match {
        case ( TBase( a, as ), TBase( b, bs ) ) if a == b =>
          apply( pairs, ( as, bs ).zipped.toList ::: rest, alreadyFixedSubst )
        case ( a: TVar, b ) if alreadyFixedSubst.typeMap.get( a ).contains( b ) =>
          apply( pairs, rest, alreadyFixedSubst )
        case ( a: TVar, b ) if !alreadyFixedSubst.typeMap.contains( a ) =>
          apply( pairs, rest, alreadyFixedSubst + ( a, b ) )
        case ( a1 -> a2, b1 -> b2 ) =>
          apply( pairs, ( a1, b1 ) :: ( a2, b2 ) :: rest, alreadyFixedSubst )
        case _ => Nil
      }
    case ( first :: rest, _ ) =>
      first match {
        case ( App( a1, b1 ), App( a2, b2 ) ) =>
          apply( ( a1 -> a2 ) :: ( b1 -> b2 ) :: rest, ( b1.ty, b2.ty ) :: tyPairs, alreadyFixedSubst )

        case ( Const( n1, t1 ), Const( n2, t2 ) ) if n1 == n2 =>
          apply( rest, ( t1, t2 ) :: tyPairs, alreadyFixedSubst )

        case ( Abs( v1, e1 ), Abs( v2, e2 ) ) =>
          val v1_ = rename(
            v1,
            alreadyFixedSubst.domain ++
              pairs.flatMap { p => freeVariables( p._1 ) ++ freeVariables( p._2 ) } toList
          )
          val v2_ = Var( v1_.name, v2.ty )
          apply(
            ( v1_ -> v2_ ) :: ( Substitution( v1 -> v1_ )( e1 ) -> Substitution( v2 -> v2_ )( e2 ) ) :: rest,
            tyPairs, alreadyFixedSubst
          ).map { subst => Substitution( subst.map - v1_ ) }

        case ( v: Var, exp ) if alreadyFixedSubst.map.get( v ).contains( exp ) =>
          apply( rest, tyPairs, alreadyFixedSubst )

        case ( v: Var, exp ) if !alreadyFixedSubst.map.contains( v ) =>
          apply( rest, ( v.ty, exp.ty ) :: tyPairs, alreadyFixedSubst + ( v, exp ) )

        case _ => Nil
      }
  }
}
