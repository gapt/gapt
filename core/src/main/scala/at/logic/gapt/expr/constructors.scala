package at.logic.gapt.expr

object NonLogicalConstant {
  def unapply( e: LambdaExpression ) = e match {
    case c: LogicalConstant => None
    case Const( n, t )      => Some( n, t )
    case _                  => None
  }
}

object HOLFunction {
  def apply( head: LambdaExpression, args: List[LambdaExpression] ): LambdaExpression = {
    val res = Apps( head, args )
    require( res.exptype != To )
    res
  }
  def unapply( e: LambdaExpression ): Option[( LambdaExpression, List[LambdaExpression] )] = e match {
    case Apps( head @ ( NonLogicalConstant( _, _ ) | Var( _, _ ) ), args ) if e.exptype != To => Some( head, args )
    case _ => None
  }
}

object FOLHeadType {
  def apply( ret: Ty, arity: Int ): Ty = arity match {
    case 0 => ret
    case n => Ti -> FOLHeadType( ret, n - 1 )
  }
  def unapply( t: Ty ): Option[( Ty, Int )] = t match {
    case Ti -> FOLHeadType( t, n ) => Some( ( t, n + 1 ) )
    case _                         => Some( ( t, 0 ) )
  }
}

object FOLFunction {
  def apply( sym: String, args: FOLTerm* )( implicit dummyImplicit: DummyImplicit ): FOLTerm = FOLFunction( sym, args )
  def apply( sym: String, args: Seq[FOLTerm] ): FOLTerm =
    Apps( FOLFunctionConst( sym, args.size ), args ).asInstanceOf[FOLTerm]

  def unapply( e: FOLTerm ): Option[( String, List[FOLTerm] )] = e match {
    case Apps( FOLFunctionConst( sym, _ ), args ) =>
      Some( ( sym, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

class QuantifierHelper( val q: QuantifierC ) {
  def apply( v: Var, formula: LambdaExpression ): HOLFormula =
    App( q( v.exptype ), Abs( v, formula ) ).asInstanceOf[HOLFormula]
  def apply( v: FOLVar, formula: FOLFormula ): FOLFormula =
    apply( v, formula.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

  def unapply( e: LambdaExpression ): Option[( Var, HOLFormula )] = e match {
    // TODO: eta-expansion?
    case App( q( _ ), Abs( v, formula: HOLFormula ) ) => Some( ( v, formula ) )
    case _ => None
  }

  def unapply( f: FOLFormula ): Option[( FOLVar, FOLFormula )] =
    unapply( f.asInstanceOf[FOLExpression] )
  def unapply( f: FOLExpression ): Option[( FOLVar, FOLFormula )] = unapply( f.asInstanceOf[LambdaExpression] ) match {
    case Some( ( v: FOLVar, formula: FOLFormula ) ) => Some( ( v, formula ) )
    case _ => None
  }

  object Block {
    def apply( vars: Seq[Var], formula: LambdaExpression ): LambdaExpression = vars match {
      case v +: vs => QuantifierHelper.this( v, apply( vs, formula ) )
      case Seq()   => formula
    }
    def apply( vars: Seq[Var], formula: HOLFormula ): HOLFormula =
      apply( vars, formula.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]
    def apply( vars: Seq[FOLVar], formula: FOLFormula ): FOLFormula =
      apply( vars, formula.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]

    private object SingleQ {
      def unapply( e: LambdaExpression ) = QuantifierHelper.this.unapply( e )
    }
    def unapply( e: LambdaExpression ): Some[( List[Var], LambdaExpression )] = e match {
      case SingleQ( v, Block( vs, f ) ) => Some( ( v :: vs, f ) )
      case _                            => Some( ( List(), e ) )
    }
    def unapply( f: HOLFormula ): Some[( List[Var], HOLFormula )] =
      unapply( f.asInstanceOf[LambdaExpression] ).asInstanceOf[Some[( List[Var], HOLFormula )]]
    def unapply( f: FOLFormula ): Some[( List[FOLVar], FOLFormula )] =
      unapply( f.asInstanceOf[LambdaExpression] ).asInstanceOf[Some[( List[FOLVar], FOLFormula )]]
  }
}

object All extends QuantifierHelper( ForallC )
object Ex extends QuantifierHelper( ExistsC )

class BinaryPropConnectiveHelper( val c: MonomorphicLogicalC ) {
  def apply( a: LambdaExpression, b: LambdaExpression ): HOLFormula =
    Apps( c(), a, b ).asInstanceOf[HOLFormula]
  def apply( a: FOLFormula, b: FOLFormula ): FOLFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula, b: PropFormula ): PropFormula =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[PropFormula]

  def unapply( formula: LambdaExpression ): Option[( HOLFormula, HOLFormula )] = formula match {
    case App( App( c(), a: HOLFormula ), b: HOLFormula ) => Some( ( a, b ) )
    case _ => None
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

class MonoidalBinaryPropConnectiveHelper( c: MonomorphicLogicalC, val neutral: MonomorphicLogicalC ) extends BinaryPropConnectiveHelper( c ) {
  def apply( fs: TraversableOnce[HOLFormula] ): HOLFormula = nAry( fs.toSeq: _* )
  def apply( fs: TraversableOnce[FOLFormula] )( implicit d: DummyImplicit ): FOLFormula = nAry( fs.toSeq: _* )

  def leftAssociative( fs: LambdaExpression* ): HOLFormula =
    fs.reduceLeftOption( super.apply ).getOrElse( neutral() ).asInstanceOf[HOLFormula]
  def leftAssociative( fs: FOLFormula* ): FOLFormula =
    leftAssociative( fs.asInstanceOf[Seq[LambdaExpression]]: _* ).asInstanceOf[FOLFormula]

  def rightAssociative( fs: LambdaExpression* ): HOLFormula =
    fs.reduceRightOption( super.apply ).getOrElse( neutral() ).asInstanceOf[HOLFormula]
  def rightAssociative( fs: FOLFormula* ): FOLFormula =
    rightAssociative( fs.asInstanceOf[Seq[LambdaExpression]]: _* ).asInstanceOf[FOLFormula]

  object nAry {
    def apply( fs: LambdaExpression* )( implicit d: DummyImplicit ): HOLFormula = leftAssociative( fs: _* )
    def apply( fs: FOLFormula* )( implicit d: DummyImplicit ): FOLFormula = leftAssociative( fs: _* )

    private object Binary {
      def unapply( formula: LambdaExpression ) = MonoidalBinaryPropConnectiveHelper.this.unapply( formula )
    }

    def unapply( formula: HOLFormula ): Some[List[HOLFormula]] = formula match {
      case Binary( nAry( as ), nAry( bs ) ) => Some( as ::: bs )
      case neutral()                        => Some( List() )
      case _                                => Some( List( formula ) )
    }

    def unapply( formula: FOLFormula ): Some[List[FOLFormula]] =
      unapply( formula.asInstanceOf[HOLFormula] ).asInstanceOf[Some[List[FOLFormula]]]
  }
}

object And extends MonoidalBinaryPropConnectiveHelper( AndC, TopC )
object Or extends MonoidalBinaryPropConnectiveHelper( OrC, BottomC )
object Imp extends BinaryPropConnectiveHelper( ImpC )

class UnaryPropConnectiveHelper( val c: MonomorphicLogicalC ) {
  def apply( a: LambdaExpression ): HOLFormula = Apps( c(), a ).asInstanceOf[HOLFormula]
  def apply( a: FOLFormula ): FOLFormula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula ): PropFormula = apply( a.asInstanceOf[LambdaExpression] ).asInstanceOf[PropFormula]

  def unapply( formula: LambdaExpression ): Option[HOLFormula] = formula match {
    case App( c(), a: HOLFormula ) => Some( a )
    case _                         => None
  }
  def unapply( formula: FOLFormula ): Option[FOLFormula] =
    unapply( formula.asInstanceOf[FOLExpression] )
  def unapply( formula: FOLExpression ): Option[FOLFormula] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case Some( a: FOLFormula ) => Some( a )
      case _                     => None
    }
  def unapply( formula: PropFormula ): Option[PropFormula] =
    unapply( formula.asInstanceOf[LambdaExpression] ) match {
      case Some( a: PropFormula ) => Some( a )
      case _                      => None
    }
}

object Neg extends UnaryPropConnectiveHelper( NegC )

class NullaryPropConnectiveHelper( val c: MonomorphicLogicalC ) {
  def apply(): PropFormula = c().asInstanceOf[PropFormula]
  def unapply( formula: PropFormula ) = formula match {
    case c() => true
    case _   => false
  }
}

object Top extends NullaryPropConnectiveHelper( TopC )
object Bottom extends NullaryPropConnectiveHelper( BottomC )

object Eq {
  def apply( a: LambdaExpression, b: LambdaExpression ): HOLAtom = Apps( EqC( a.exptype ), a, b ).asInstanceOf[HOLAtom]
  def apply( a: FOLTerm, b: FOLTerm ): FOLAtom =
    apply( a, b.asInstanceOf[LambdaExpression] ).asInstanceOf[FOLAtom]

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
