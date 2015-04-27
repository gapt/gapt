package at.logic.gapt.expr
import types._

object UndistinguishedConstant {
  def unapply( e: LambdaExpression ) = e match {
    case c: DistinguishedConstant => None
    case Const( n, t )            => Some( n, t )
    case _                        => None
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
  def apply( v: Var, formula: LambdaExpression ): LambdaExpression =
    App( q( v.exptype ), Abs( v, formula ) )
  def apply( v: FOLVar, formula: FOLFormula ): FOLFormula =
    apply( v, formula.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

  def unapply( e: LambdaExpression ): Option[( Var, LambdaExpression )] = e match {
    // TODO: eta-expansion?
    case App( q( _ ), Abs( v, formula ) ) => Some( ( v, formula ) )
    case _                                => None
  }

  def unapply( f: FOLFormula ): Option[( FOLVar, FOLFormula )] = unapply( f.asInstanceOf[LambdaExpression] ) match {
    case Some( ( v: FOLVar, formula: FOLFormula ) ) => Some( ( v, formula ) )
    case _ => None
  }
}

object All extends QuantifierHelper( ForallQ )
object Ex extends QuantifierHelper( ExistsQ )

class BinaryFOLConnectiveHelper( val c: LogicalC ) {
  def apply( a: LambdaExpression, b: LambdaExpression ): LambdaExpression =
    Apps( c(), a, b )
  def apply( a: Formula, b: Formula ): Formula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[Formula]
  def apply( a: SchematicFormula, b: SchematicFormula ): SchematicFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[SchematicFormula]
  def apply( a: FOLFormula, b: FOLFormula ): FOLFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula, b: PropFormula ): PropFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[PropFormula]

  def unapply( formula: LambdaExpression ): Option[( LambdaExpression, LambdaExpression )] = formula match {
    case App( App( c(), a ), b ) => Some( ( a, b ) )
    case _                       => None
  }
  def unapply( formula: Formula ): Option[( Formula, Formula )] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case Some( ( a: Formula, b: Formula ) ) => Some( ( a, b ) )
      case _                                  => None
    }
  def unapply( formula: SchematicFormula ): Option[( SchematicFormula, SchematicFormula )] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case Some( ( a: SchematicFormula, b: SchematicFormula ) ) => Some( ( a, b ) )
      case _ => None
    }
  def unapply( formula: FOLFormula ): Option[( FOLFormula, FOLFormula )] =
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

object And extends BinaryFOLConnectiveHelper( AndC )
object Or extends BinaryFOLConnectiveHelper( OrC )
object Imp extends BinaryFOLConnectiveHelper( ImpC )

object Ands {
  def apply( conjs: LambdaExpression* ): LambdaExpression = conjs match {
    case Seq()                  => TopC()
    case Seq( conj )            => conj
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

class UnaryFOLConnectiveHelper( val c: LogicalC ) {
  def apply( a: LambdaExpression ): LambdaExpression = Apps( c(), a )
  def apply( a: Formula ): Formula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[Formula]
  def apply( a: SchematicFormula ): SchematicFormula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[SchematicFormula]
  def apply( a: FOLFormula ): FOLFormula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula ): PropFormula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[PropFormula]

  def unapply( formula: LambdaExpression ): Option[LambdaExpression] = formula match {
    case App( c(), a ) => Some( a )
    case _             => None
  }
  def unapply( formula: Formula ): Option[Formula] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case a: Formula => Some( a )
      case _          => None
    }
  def unapply( formula: SchematicFormula ): Option[SchematicFormula] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case a: SchematicFormula => Some( a )
      case _                   => None
    }
  def unapply( formula: FOLFormula ): Option[FOLFormula] =
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
    case c() => Some()
    case _   => None
  }
}

object Eq {
  def apply( a: LambdaExpression, b: LambdaExpression ): Formula = Apps( EqC( a.exptype ), a, b ).asInstanceOf[Formula]
  def apply( a: SchematicIntTerm, b: SchematicIntTerm ): SchematicFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[SchematicFormula]
  def apply( a: FOLTerm, b: FOLTerm ): FOLFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

  def unapply( e: LambdaExpression ): Option[( LambdaExpression, LambdaExpression )] = e match {
    case App( App( EqC( _ ), a ), b ) => Some( a, b )
    case _                            => None
  }
  def unapply( f: FOLFormula ): Option[( FOLTerm, FOLTerm )] = f.asInstanceOf[LambdaExpression] match {
    case Eq( a: FOLTerm, b: FOLTerm ) => Some( a, b )
    case _                            => None
  }
}

package schematic {

  class BigConnectiveHelper( val c: LogicalC ) {
    def apply( v: Var, a: LambdaExpression, from: LambdaExpression, to: LambdaExpression ): LambdaExpression =
      Apps( c(), Abs( v, a ), from, to )
    def apply( v: SchematicVar, a: SchematicFormula, from: SchematicIntTerm, to: SchematicIntTerm ): SchematicFormula =
      apply( v, a.asInstanceOf[LambdaExpression], from, to ).asInstanceOf[SchematicFormula]

    def unapply( formula: LambdaExpression ): Option[( Var, LambdaExpression, LambdaExpression, LambdaExpression )] = formula match {
      case App( App( App( c(), Abs( v, a ) ), from ), to ) => Some( ( v, a, from, to ) )
      case _ => None
    }
    def unapply( formula: SchematicFormula ): Option[( SchematicVar, SchematicFormula, SchematicIntTerm, SchematicIntTerm )] =
      unapply( formula.asInstanceOf[LambdaExpression] ) match {
        case Some( ( v, a, from, to ) ) => Some( (
          v.asInstanceOf[SchematicVar], a.asInstanceOf[SchematicFormula],
          from.asInstanceOf[SchematicIntTerm], to.asInstanceOf[SchematicIntTerm] ) )
        case _ => None
      }
  }

  object BigAnd extends BigConnectiveHelper( BigAndC )
  object BigOr extends BigConnectiveHelper( BigOrC )

  object Succ {
    def apply( t: SchematicIntTerm ): SchematicIntTerm = App( SuccC(), t ).asInstanceOf[SchematicIntTerm]
    def unapply( p: SchematicIntTerm ) = p match {
      case App( SuccC(), t: SchematicIntTerm ) => Some( t )
      case _                                   => None
    }
  }

  object lessThan {
    def apply( left: SchematicIntTerm, right: SchematicIntTerm ) =
      Apps( LessThanC(), left, right ).asInstanceOf[SchematicFormula]

    def unapply( expression: SchematicFormula ) = expression match {
      case App( App( LessThanC(), left ), right ) => Some( left, right )
      case _                                      => None
    }
  }

  object leq {
    def apply( left: SchematicIntTerm, right: SchematicIntTerm ) =
      App( App( LeqC(), left ), right ).asInstanceOf[SchematicFormula]

    def unapply( expression: SchematicFormula ) = expression match {
      case App( App( LeqC(), left ), right ) => Some( left, right )
      case _                                 => None
    }
  }

}
