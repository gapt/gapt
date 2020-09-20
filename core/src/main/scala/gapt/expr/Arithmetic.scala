package gapt.expr

package object arithmetic {

  //TODO: merge with logical operators
  case class BinaryArithmeticOp( val argtype: Ty, val connective: Const ) {
    require( connective.ty match { case t1 ->: ( t2 ->: _ ) => ( t1 == argtype ) && ( t1 == t2 ); case _ => false } )

    def apply( s: Expr, t: Expr ): Expr = {
      App( connective, Seq( s, t ) )
    }

    def unapply( s: Expr ): Option[( Expr, Expr )] = s match {
      case App( App( c, s ), t ) if c == connective => Some( ( s, t ) )
      case _                                        => None
    }
  }

  case class UnaryArithmeticOp( val argtype: Ty, val connective: Const ) {
    require( connective.ty match { case t1 ->: _ => t1 == argtype; case _ => false } )

    def apply( t: Expr ): Expr = {
      App( connective, Seq( t ) )
    }

    def unapply( s: Expr ): Option[Expr] = s match {
      case App( c, t ) if c == connective => Some( t )
      case _                              => None
    }
  }

  class MonoidalArithmeticOp( override val argtype: Ty, val neutral: Const, override val connective: Const ) extends BinaryArithmeticOp( argtype, connective ) {
    def apply( seq: Seq[Expr] ): Expr =
      if ( seq.isEmpty ) neutral else seq.tail.foldLeft( seq.head )( ( x, y ) => apply( y, x ) )

    def nAry( e: Expr ): Seq[Expr] = e match {
      case App( c, App( s, t ) ) if c == connective =>
        nAry( s ) ++ nAry( t )
      case _ => Seq( e )
    }

  }

  object int {
    object TInt extends TBase( "$int", Nil )

    val Zero = Const( "0", TInt )
    val One = Const( "1", TInt )

    val SumC = Const( "$sum", TInt ->: ( TInt ->: TInt ) )
    val ProductC = Const( "$product", TInt ->: ( TInt ->: TInt ) )
    val DifferenceC = Const( "$difference", TInt ->: ( TInt ->: TInt ) )
    val UnaryMinusC = Const( "$uminus", TInt ->: TInt )
    val LessC = Const( "$less", TInt ->: ( TInt ->: To ) )
    val LessEqC = Const( "$lesseq", TInt ->: ( TInt ->: To ) )
    val GreaterC = Const( "$greater", TInt ->: ( TInt ->: To ) )
    val GreaterEqC = Const( "$greatereq", TInt ->: ( TInt ->: To ) )

    object Sum extends MonoidalArithmeticOp( TInt, Zero, SumC )
    object Product extends MonoidalArithmeticOp( TInt, One, ProductC )
    object Less extends BinaryArithmeticOp( TInt, LessC )
    object LessEq extends BinaryArithmeticOp( TInt, LessC )
    object Greater extends BinaryArithmeticOp( TInt, LessC )
    object GreaterEq extends BinaryArithmeticOp( TInt, LessC )
  }

  object real {

    object TReal extends TBase( "$real", Nil )

  }

  object rational {

    object TRational extends TBase( "$rat", Nil )

  }

}