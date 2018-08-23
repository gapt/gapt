package gapt.expr

object syntacticMGU {
  private type Nullable[T] = T

  private def go( a: Ty, b: Ty, subst: PreSubstitution, bound: Set[Var] ): Nullable[PreSubstitution] =
    ( a, b ) match {
      case _ if a eq b => subst

      case ( a1 ->: a2, b1 ->: b2 ) =>
        go( a1, b1, subst, bound ) match {
          case null   => null
          case subst1 => go( a2, b2, subst1, bound )
        }

      case ( TBase( n1, ts1 ), TBase( n2, ts2 ) ) =>
        if ( n1 != n2 ) null else go( ts1, ts2, subst, bound )

      case ( x: TVar, t ) =>
        subst.typeMap.get( x ) match {
          case Some( x_ ) => go( x_, t, subst, bound )
          case None =>
            val t_ = subst.toSubstitution( t )
            if ( x == t_ ) {
              subst
            } else if ( typeVariables( t_ ).contains( x ) ) {
              null
            } else {
              val subst1 = Substitution( Map(), Map( x -> t_ ) )
              new PreSubstitution(
                Map() ++ subst.map.mapValues( subst1( _ ) ),
                Map() ++ subst.typeMap.mapValues( subst1( _ ) ) + ( x -> t_ ) )
            }
        }

      case ( y, x: TVar ) => go( x, y, subst, bound )

      case _              => null
    }

  private def go( as: List[Ty], bs: List[Ty], subst: PreSubstitution, bound: Set[Var] ): Nullable[PreSubstitution] =
    ( as, bs ) match {
      case ( Nil, Nil ) => subst
      case ( a :: ass, b :: bss ) =>
        go( a, b, subst, bound ) match {
          case null   => null
          case subst1 => go( ass, bss, subst1, bound )
        }
      case _ => null
    }

  private def go( a: Expr, b: Expr, subst: PreSubstitution, bound: Set[Var] ): Nullable[PreSubstitution] =
    ( a, b ) match {
      case _ if a eq b => subst

      case ( App( a1, a2 ), App( b1, b2 ) ) =>
        go( a1, b1, subst, bound ) match {
          case null => null
          case subst1 =>
            go( a2, b2, subst1, bound )
        }

      case ( Const( n1, t1, ps1 ), Const( n2, t2, ps2 ) ) =>
        if ( n1 != n2 ) null else
          go( t1, t2, subst, bound ) match {
            case null => null
            case subst1 =>
              go( ps1, ps2, subst1, bound )
          }

      case ( Abs( v1, e1 ), Abs( v2, e2 ) ) =>
        if ( v1.ty == v2.ty ) {
          val v1_ = rename( v1, subst.domain ++ subst.range ++ freeVariables( List( a, b ) ) )
          val v2_ = v1_
          go( Substitution( v1 -> v1_ )( e1 ), Substitution( v2 -> v2_ )( e2 ), subst, bound + v1_ ) match {
            case null => null
            case subst2 =>
              new PreSubstitution( subst2.map - v1_, subst2.typeMap )
          }
        } else go( v1.ty, v2.ty, subst, bound ) match {
          case null => null
          case subst1 =>
            val subst1_ = subst1.toSubstitution
            go( subst1_( a ), subst1_( b ), subst1, bound )
        }

      case ( x: Var, y ) if bound.contains( x ) =>
        if ( x == y ) subst else null

      case ( x: Var, t ) =>
        subst.map.get( x ) match {
          case Some( x_ ) => go( x_, t, subst, bound )
          case None =>
            val t_ = subst.toSubstitution( t )
            if ( x == t_ ) {
              subst
            } else if ( freeVariables( t_ ) intersect ( bound + x ) nonEmpty ) {
              null
            } else if ( x.ty == t_.ty ) {
              val subst1 = Substitution( x -> t_ )
              new PreSubstitution( Map() ++ subst.map.mapValues( subst1( _ ) ) + ( x -> t_ ), subst.typeMap )
            } else {
              go( x.ty, t_.ty, subst, bound ) match {
                case null => null
                case subst1 =>
                  val subst1_ = subst1.toSubstitution
                  go( subst1_( x ), subst1_( t_ ), subst, bound )
              }
            }
        }

      case ( y, x: Var ) => go( x, y, subst, bound )

      case _             => null
    }

  def apply( exprs: Iterable[Expr] )( implicit dummyImplicit: DummyImplicit ): Option[Substitution] = {
    val exprs_ = exprs.toSeq
    apply( exprs_ zip exprs_.tail )
  }
  def apply( eqs: Iterable[( Expr, Expr )] ): Option[Substitution] = {
    var subst: Nullable[PreSubstitution] = PreSubstitution()
    eqs.foreach { case ( l, r ) => if ( subst != null ) subst = go( l, r, subst, Set.empty[Var] ) }
    subst match {
      case null => None
      case _    => Some( subst.toSubstitution )
    }
  }
  def apply( a: Expr, b: Expr ): Option[Substitution] =
    go( a, b, PreSubstitution(), Set.empty[Var] ) match {
      case null  => None
      case subst => Some( subst.toSubstitution )
    }

  def apply( eqs: Iterable[( FOLExpression, FOLExpression )] )( implicit dummyImplicit: DummyImplicit, dummyImplicit2: DummyImplicit ): Option[FOLSubstitution] =
    apply( eqs: Iterable[( Expr, Expr )] ).map( _.asFOLSubstitution )
  def apply( a: FOLExpression, b: FOLExpression ): Option[FOLSubstitution] =
    apply( a: Expr, b ).map( _.asFOLSubstitution )

  def apply( a: Expr, b: Expr, treatAsConstant: Set[Var] ): Option[Substitution] = {
    val nameGen = rename.awayFrom( constants( a ) ++ constants( b ) )
    val grounding = treatAsConstant.map( v => v -> nameGen.fresh( Const( v.name, v.ty ) ) )
    apply( Substitution( grounding )( a ), Substitution( grounding )( b ) ).map( mgu =>
      TermReplacement( mgu, grounding.map( _.swap ).toMap ) )
  }

}
