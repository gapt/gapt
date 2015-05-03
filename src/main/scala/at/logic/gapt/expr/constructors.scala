package at.logic.gapt.expr
import types._

object UndistinguishedConstant {
  def unapply( e: LambdaExpression ) = e match {
    case c: DistinguishedConstant => None
    case Const( n, t )            => Some( n, t )
    case _                        => None
  }
}

object HOLAtom {
  def apply( head: LambdaExpression, args: LambdaExpression* ): Formula =
    apply( head, args toList )
  def apply( head: LambdaExpression, args: List[LambdaExpression] ): Formula =
    Apps( head, args ).asInstanceOf[Formula]
  def unapply( e: LambdaExpression ): Option[( LambdaExpression, List[LambdaExpression] )] = e match {
    case Apps( head, args ) if e.exptype == To => Some( head, args )
    case _                                     => None
  }
}

object HOLFunction {
  def apply( head: LambdaExpression, args: List[LambdaExpression] ): LambdaExpression = {
    val res = Apps( head, args )
    require( res.exptype != To )
    res
  }
  def unapply( e: LambdaExpression ): Option[( LambdaExpression, List[LambdaExpression] )] = e match {
    case Apps( head, args ) if e.exptype != To => Some( head, args )
    case _                                     => None
  }
}

object FOLHeadType {
  def apply( ret: TA, arity: Int ): TA = arity match {
    case 0 => ret
    case n => Ti -> FOLHeadType( ret, n - 1 )
  }
  def unapply( t: TA ): Option[( TA, Int )] = t match {
    case Ti -> FOLHeadType( t, n ) => Some( ( t, n + 1 ) )
    case _                         => Some( ( t, 0 ) )
  }
}

object FOLAtom {
  def apply( sym: String, args: FOLTerm* ): FOLFormula = FOLAtom( sym, args toList )
  def apply( sym: String, args: List[FOLTerm] ): FOLFormula =
    Apps( Const( sym, FOLHeadType( To, args.length ) ), args ).asInstanceOf[FOLFormula]

  def unapply( e: LambdaExpression ): Option[( String, List[FOLTerm] )] = e match {
    case Apps( UndistinguishedConstant( sym, FOLHeadType( To, _ ) ), args ) if e.isInstanceOf[FOLFormula] =>
      Some( ( sym, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

object FOLFunction {
  def apply( sym: String, args: FOLTerm* ): FOLTerm = FOLFunction( sym, args toList )
  def apply( sym: String, args: List[FOLTerm] ): FOLTerm =
    Apps( Const( sym, FOLHeadType( Ti, args.length ) ), args ).asInstanceOf[FOLTerm]

  def unapply( e: LambdaExpression ): Option[( String, List[FOLTerm] )] = e match {
    case Apps( UndistinguishedConstant( sym, FOLHeadType( Ti, _ ) ), args ) if e.isInstanceOf[FOLTerm] =>
      Some( ( sym, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

class QuantifierHelper( val q: QuantifierC ) {
  def apply( v: Var, formula: LambdaExpression ): Formula =
    App( q( v.exptype ), Abs( v, formula ) ).asInstanceOf[Formula]
  def apply( v: FOLVar, formula: FOLFormula ): FOLFormula =
    apply( v, formula.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

  def unapply( e: LambdaExpression ): Option[( Var, Formula )] = e match {
    // TODO: eta-expansion?
    case App( q( _ ), Abs( v, formula: Formula ) ) => Some( ( v, formula ) )
    case _                                         => None
  }

  def unapply( f: FOLFormula ): Option[( FOLVar, FOLFormula )] =
    unapply( f.asInstanceOf[FOLExpression] )
  def unapply( f: FOLExpression ): Option[( FOLVar, FOLFormula )] = unapply( f.asInstanceOf[LambdaExpression] ) match {
    case Some( ( v: FOLVar, formula: FOLFormula ) ) => Some( ( v, formula ) )
    case _ => None
  }
}

object All extends QuantifierHelper( ForallQ )
object Ex extends QuantifierHelper( ExistsQ )

class BinaryFOLConnectiveHelper( val c: LogicalC ) {
  def apply( a: LambdaExpression, b: LambdaExpression ): Formula =
    Apps( c(), a, b ).asInstanceOf[Formula]
  def apply( a: FOLFormula, b: FOLFormula ): FOLFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula, b: PropFormula ): PropFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[PropFormula]

  def unapply( formula: LambdaExpression ): Option[( Formula, Formula )] = formula match {
    case App( App( c(), a: Formula ), b: Formula ) => Some( ( a, b ) )
    case _                                         => None
  }
  def unapply( formula: FOLFormula ): Option[( FOLFormula, FOLFormula )] =
    unapply( formula.asInstanceOf[FOLExpression] )
  def unapply( formula: FOLExpression ): Option[( FOLFormula, FOLFormula )] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case Some( ( a: FOLFormula, b: FOLFormula ) ) => Some( ( a, b ) )
      case _                                        => None
    }
  def unapply( formula: PropFormula ): Option[( PropFormula, PropFormula )] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case Some( ( a: PropFormula, b: PropFormula ) ) => Some( ( a, b ) )
      case _ => None
    }
}

object And extends BinaryFOLConnectiveHelper( AndC ) {
  def apply( conjs: List[Formula] ): Formula = Ands( conjs: _* )
  def apply( conjs: List[FOLFormula] )( implicit d: DummyImplicit ): FOLFormula = Ands( conjs: _* )
}
object Or extends BinaryFOLConnectiveHelper( OrC ) {
  def apply( conjs: List[Formula] ): Formula = Ors( conjs: _* )
  def apply( conjs: List[FOLFormula] )( implicit d: DummyImplicit ): FOLFormula = Ors( conjs: _* )
}
object Imp extends BinaryFOLConnectiveHelper( ImpC )

object Ands {
  def apply( conjs: LambdaExpression* ): Formula = conjs match {
    case Seq()                  => Top()
    case Seq( conj )            => conj.asInstanceOf[Formula]
    case Seq( conj, rest @ _* ) => And( conj, Ands( rest: _* ) )
  }
  def apply( conjs: FOLFormula* ): FOLFormula =
    Ands( conjs.asInstanceOf[Seq[LambdaExpression]]: _* ).asInstanceOf[FOLFormula]

  def unapply( formula: LambdaExpression ): Some[List[LambdaExpression]] = formula match {
    case And( Ands( as ), Ands( bs ) ) => Some( as ::: bs )
    case a                             => Some( List( a ) )
  }
  def unapply( formula: FOLFormula ): Some[List[FOLFormula]] = formula match {
    case And( Ands( as ), Ands( bs ) ) => Some( as ::: bs )
    case a                             => Some( List( a ) )
  }
}

object Ors {
  def apply( conjs: LambdaExpression* ): Formula = conjs match {
    case Seq()                  => Top()
    case Seq( conj )            => conj.asInstanceOf[Formula]
    case Seq( conj, rest @ _* ) => Or( conj, Ors( rest: _* ) )
  }
  def apply( conjs: FOLFormula* ): FOLFormula =
    Ors( conjs.asInstanceOf[Seq[LambdaExpression]]: _* ).asInstanceOf[FOLFormula]

  def unapply( formula: LambdaExpression ): Some[List[LambdaExpression]] = formula match {
    case Or( Ors( as ), Ors( bs ) ) => Some( as ::: bs )
    case a                          => Some( List( a ) )
  }
  def unapply( formula: FOLFormula ): Some[List[FOLFormula]] = formula match {
    case Or( Ors( as ), Ors( bs ) ) => Some( as ::: bs )
    case a                          => Some( List( a ) )
  }
}

class UnaryFOLConnectiveHelper( val c: LogicalC ) {
  def apply( a: LambdaExpression ): Formula = Apps( c(), a ).asInstanceOf[Formula]
  def apply( a: FOLFormula ): FOLFormula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula ): PropFormula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[PropFormula]

  def unapply( formula: LambdaExpression ): Option[Formula] = formula match {
    case App( c(), a: Formula ) => Some( a )
    case _                      => None
  }
  def unapply( formula: FOLFormula ): Option[FOLFormula] =
    unapply( formula.asInstanceOf[FOLExpression] )
  def unapply( formula: FOLExpression ): Option[FOLFormula] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case a: FOLFormula => Some( a )
      case _             => None
    }
  def unapply( formula: PropFormula ): Option[PropFormula] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case a: PropFormula => Some( a )
      case _              => None
    }
}

object Neg extends UnaryFOLConnectiveHelper( NegC )

class NullaryFOLConnective( val c: LogicalC ) {
  def apply(): PropFormula = c().asInstanceOf[PropFormula]
  def unapply( formula: LambdaExpression ) = formula match {
    case c() => true
    case _   => false
  }
}

object Top extends NullaryFOLConnective( TopC )
object Bottom extends NullaryFOLConnective( BottomC )

object Eq {
  def apply( a: LambdaExpression, b: LambdaExpression ): Formula = Apps( EqC( a.exptype ), a, b ).asInstanceOf[Formula]
  def apply( a: FOLTerm, b: FOLTerm ): FOLFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

  def unapply( e: LambdaExpression ): Option[( LambdaExpression, LambdaExpression )] = e match {
    case App( App( EqC( _ ), a ), b ) => Some( a, b )
    case _                            => None
  }
  def unapply( f: FOLFormula ): Option[( FOLTerm, FOLTerm )] = unapply( f.asInstanceOf[FOLExpression] )
  def unapply( f: FOLExpression ): Option[( FOLTerm, FOLTerm )] = f.asInstanceOf[LambdaExpression] match {
    case Eq( a: FOLTerm, b: FOLTerm ) => Some( a, b )
    case _                            => None
  }
}
