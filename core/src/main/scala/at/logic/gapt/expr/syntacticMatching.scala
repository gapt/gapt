package at.logic.gapt.expr

object syntacticMatching {

  def apply( from: FOLExpression, to: FOLExpression ): Option[FOLSubstitution] =
    apply( List( from -> to ) )

  def apply( pairs: List[( FOLExpression, FOLExpression )] )( implicit dummyImplicit: DummyImplicit ): Option[FOLSubstitution] =
    apply( pairs, Map[FOLVar, FOLTerm]() )

  def apply(
    pairs:             List[( FOLExpression, FOLExpression )],
    alreadyFixedSubst: Map[FOLVar, FOLTerm]
  )( implicit dummyImplicit: DummyImplicit ): Option[FOLSubstitution] =
    apply(
      pairs.asInstanceOf[List[( LambdaExpression, LambdaExpression )]],
      alreadyFixedSubst.asInstanceOf[Map[Var, LambdaExpression]]
    ) map { subst =>
      FOLSubstitution( subst.map map { case ( l: FOLVar, r: FOLTerm ) => l -> r } )
    }

  def apply( from: LambdaExpression, to: LambdaExpression ): Option[Substitution] =
    apply( List( from -> to ) )

  def apply( pairs: List[( LambdaExpression, LambdaExpression )] ): Option[Substitution] =
    apply( pairs, Map[Var, LambdaExpression]() )

  /**
   * Recursively looks for a Substitution σ such that for each (a, b) ∈ pairs, σ(a) = b.
   *
   * @param pairs A list of pairs of expressions.
   * @param alreadyFixedSubst The partial substitution which is already fixed, and can no longer be changed.
   * @return
   */
  def apply(
    pairs:             List[( LambdaExpression, LambdaExpression )],
    alreadyFixedSubst: Map[Var, LambdaExpression]
  ): Option[Substitution] = pairs match {
    case Nil => Some( Substitution( alreadyFixedSubst ) )
    case first :: rest =>
      first match {
        case ( a, b ) if a.exptype != b.exptype => None

        case ( App( a1, b1 ), App( a2, b2 ) ) if b1.exptype == b2.exptype =>
          apply( ( a1 -> a2 ) :: ( b1 -> b2 ) :: rest, alreadyFixedSubst )

        case ( c1: Const, c2: Const ) if c1 == c2 => apply( rest, alreadyFixedSubst )

        case ( a1 @ Abs( v1, e1 ), a2 @ Abs( v2, e2 ) ) if v1.exptype == v2.exptype =>
          val v_ = rename(
            v1,
            alreadyFixedSubst.keySet ++
              pairs.flatMap { p => freeVariables( p._1 ) ++ freeVariables( p._2 ) } toList
          )
          apply( ( Substitution( v1 -> v_ )( e1 ) -> Substitution( v2 -> v_ )( e2 ) ) :: rest, alreadyFixedSubst )

        case ( v: Var, exp ) if alreadyFixedSubst.get( v ).contains( exp ) =>
          apply( rest, alreadyFixedSubst )

        case ( v: Var, exp ) if !alreadyFixedSubst.contains( v ) =>
          apply( rest, alreadyFixedSubst + ( v -> exp ) )

        case _ => None
      }
  }
}
