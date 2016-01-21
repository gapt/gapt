package at.logic.gapt.expr

object syntacticMGU {
  private def unify( eqs: List[( LambdaExpression, LambdaExpression )], env: Map[Var, LambdaExpression], bound: Set[Var] ): Option[Substitution] = eqs match {
    case Nil => Some( Substitution( env ) )
    case first :: rest => first match {
      case ( a, b ) if a.exptype != b.exptype                           => None
      case ( App( a1, b1 ), App( a2, b2 ) ) if b1.exptype == b2.exptype => unify( ( a1 -> a2 ) :: ( b1 -> b2 ) :: rest, env, bound )
      case ( c1: Const, c2: Const ) if c1 == c2                         => unify( rest, env, bound )
      case ( Abs( v1, t1 ), Abs( v2, t2 ) ) if v1.exptype == v2.exptype =>
        val v_ = rename( v1, ( env ++ eqs ).flatMap { p => freeVariables( p._1 ) ++ freeVariables( p._2 ) } ++ bound toList )
        unify( ( Substitution( v1 -> v_ )( t1 ) -> Substitution( v2 -> v_ )( t2 ) ) :: rest, env, bound + v_ )
      case ( x: Var, y ) if bound contains x =>
        if ( x == y ) unify( rest, env, bound ) else None
      case ( x: Var, t ) =>
        if ( env contains x ) {
          unify( ( env( x ) -> t ) :: rest, env, bound )
        } else {
          val t_ = Substitution( env )( t )
          if ( x == t_ ) {
            unify( rest, env, bound )
          } else if ( freeVariables( t_ ) intersect ( bound + x ) nonEmpty ) {
            None
          } else {
            val subst = Substitution( x -> t_ )
            unify( rest, ( env mapValues { subst( _ ) } ) + ( x -> t_ ), bound )
          }
        }
      case ( exp, v: Var ) => unify( ( v -> exp ) :: rest, env, bound )
      case _               => None
    }
  }

  def apply( exprs: TraversableOnce[LambdaExpression] )( implicit dummyImplicit: DummyImplicit ): Option[Substitution] = {
    val exprs_ = exprs.toSeq
    apply( exprs_ zip exprs_.tail )
  }
  def apply( eqs: TraversableOnce[( LambdaExpression, LambdaExpression )] ): Option[Substitution] = unify( eqs toList, Map(), Set() )
  def apply( a: LambdaExpression, b: LambdaExpression ): Option[Substitution] = apply( List( a -> b ) )

  def apply( eqs: TraversableOnce[( FOLExpression, FOLExpression )] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Option[FOLSubstitution] =
    unify( eqs toList, Map(), Set() ) map { subst =>
      FOLSubstitution( subst.map map { case ( l: FOLVar, r: FOLTerm ) => l -> r } )
    }
  def apply( a: FOLExpression, b: FOLExpression ): Option[FOLSubstitution] = apply( List( a -> b ) )
}
