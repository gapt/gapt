package gapt.expr

object syntacticMatching {
  private type Nullable[T] = T

  private def go( a: Ty, b: Ty, subst: PreSubstitution ): Nullable[PreSubstitution] =
    ( a, b ) match {
      case ( TBase( an, as ), TBase( bn, bs ) ) if an == bn =>
        go( as, bs, subst )
      case ( a: TVar, _ ) if subst.typeMap.get( a ).contains( b ) =>
        subst
      case ( a: TVar, _ ) if !subst.typeMap.contains( a ) =>
        subst + ( a, b )
      case ( a1 ->: a2, b1 ->: b2 ) =>
        go( a1, b1, subst ) match {
          case null   => null
          case subst1 => go( a2, b2, subst1 )
        }
      case _ => null
    }

  private def go( as: List[Ty], bs: List[Ty], subst: PreSubstitution ): Nullable[PreSubstitution] =
    ( as, bs ) match {
      case ( a :: as_, b :: bs_ ) =>
        go( a, b, subst ) match {
          case null   => null
          case subst1 => go( as_, bs_, subst1 )
        }
      case ( Nil, Nil ) => subst
      case _            => null
    }

  private def go( a: Expr, b: Expr, subst: PreSubstitution ): Nullable[PreSubstitution] =
    ( a, b ) match {
      case ( App( a1, b1 ), App( a2, b2 ) ) =>
        go( a1, a2, subst ) match {
          case null   => null
          case subst1 => go( b1, b2, subst1 )
        }

      case ( Const( n1, _, ps1 ), Const( n2, _, ps2 ) ) if n1 == n2 =>
        go( ps1, ps2, subst )

      case ( Abs( v1, e1 ), Abs( v2, e2 ) ) =>
        go( v1.ty, v2.ty, subst ) match {
          case null => null
          case subst1 =>
            val v1_ = rename( v1, subst1.domain ++ subst1.range ++ freeVariables( List( a, b ) ) )
            val v2_ = Var( v1_.name, v2.ty )
            go( Substitution( v1 -> v1_ )( e1 ), Substitution( v2 -> v2_ )( e2 ), subst1 + ( v1_, v2_ ) ) match {
              case null => null
              case subst2 =>
                new PreSubstitution( subst2.map - v1_, subst2.typeMap )
            }
        }

      case ( v: Var, exp ) if subst.map.get( v ).contains( exp ) =>
        subst

      case ( v: Var, exp ) if !subst.map.contains( v ) =>
        go( v.ty, exp.ty, subst ) match {
          case null   => null
          case subst1 => subst1 + ( v, exp )
        }

      case _ => null
    }

  def apply( from: Expr, to: Expr ): Option[Substitution] =
    apply( from, to, PreSubstitution() )

  def apply( from: Expr, to: Expr, alreadyFixed: PreSubstitution ): Option[Substitution] =
    go( from, to, alreadyFixed ) match {
      case null  => None
      case subst => Some( subst.toSubstitution )
    }

  def apply(
    pairs:        Iterable[( Expr, Expr )],
    alreadyFixed: PreSubstitution ): Option[Substitution] = {
    var subst: Nullable[PreSubstitution] = alreadyFixed
    pairs.foreach { case ( a, b ) => if ( subst != null ) subst = go( a, b, subst ) }
    subst match {
      case null => None
      case _    => Some( subst.toSubstitution )
    }
  }

  def apply( from: FOLExpression, to: FOLExpression ): Option[FOLSubstitution] =
    apply( from: Expr, to ).map( _.asFOLSubstitution )

  def apply( pairs: Iterable[( FOLExpression, FOLExpression )] )( implicit dummyImplicit: DummyImplicit ): Option[FOLSubstitution] =
    apply( pairs, Map[FOLVar, FOLTerm]() )

  def apply(
    pairs:        Iterable[( FOLExpression, FOLExpression )],
    alreadyFixed: Map[FOLVar, FOLTerm] )( implicit dummyImplicit: DummyImplicit ): Option[FOLSubstitution] =
    apply(
      pairs: Iterable[( Expr, Expr )],
      PreSubstitution( alreadyFixed ) ).map( _.asFOLSubstitution )

  def apply( pairs: List[( Expr, Expr )] ): Option[Substitution] =
    apply( pairs, PreSubstitution() )

  def apply(
    pairs: Iterable[( Ty, Ty )] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Option[Substitution] =
    apply( pairs, PreSubstitution() )( DummyImplicit.dummyImplicit )

  def apply(
    pairs:        Iterable[( Ty, Ty )],
    alreadyFixed: PreSubstitution )( implicit dummyImplicit: DummyImplicit ): Option[Substitution] = {
    var subst: Nullable[PreSubstitution] = alreadyFixed
    pairs.foreach { case ( a, b ) => if ( subst != null ) subst = go( a, b, subst ) }
    subst match {
      case null => None
      case _    => Some( subst.toSubstitution )
    }
  }

  def apply( from: Ty, to: Ty ): Option[Substitution] =
    go( from, to, PreSubstitution() ) match {
      case null  => None
      case subst => Some( subst.toSubstitution )
    }
}
