package at.logic.gapt.expr

object NonLogicalConstant {
  def unapply( c: Const ) = c match {
    case c: LogicalConstant => None
    case Const( n, t, ps )  => Some( ( n, t, ps ) )
  }
}

object HOLFunction {
  def apply( head: Expr, args: List[Expr] ): Expr = {
    val res = Apps( head, args )
    require( res.ty != To )
    res
  }
  def unapply( e: Expr ): Option[( Expr, List[Expr] )] = e match {
    case Apps( head @ ( NonLogicalConstant( _, _, _ ) | Var( _, _ ) ), args ) if e.ty != To => Some( head, args )
    case _ => None
  }
}

object FOLHeadType {
  def apply( ret: Ty, arity: Int ): Ty = arity match {
    case 0 => ret
    case n => Ti ->: FOLHeadType( ret, n - 1 )
  }
  def unapply( t: Ty ): Option[( Ty, Int )] = t match {
    case Ti ->: FOLHeadType( t, n ) => Some( ( t, n + 1 ) )
    case _                          => Some( ( t, 0 ) )
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
  def apply( v: Var, formula: Expr ): Formula =
    App( q( v.ty ), Abs( v, formula ) ).asInstanceOf[Formula]
  def apply( v: FOLVar, formula: FOLFormula ): FOLFormula =
    apply( v, formula.asInstanceOf[Expr] ).asInstanceOf[FOLFormula]

  def unapply( e: Expr ): Option[( Var, Formula )] = e match {
    // TODO: eta-expansion?
    case App( q( _ ), Abs( v, formula: Formula ) ) => Some( ( v, formula ) )
    case _                                         => None
  }

  def unapply( f: FOLFormula ): Option[( FOLVar, FOLFormula )] =
    unapply( f.asInstanceOf[FOLExpression] )
  def unapply( f: FOLExpression ): Option[( FOLVar, FOLFormula )] = unapply( f.asInstanceOf[Expr] ) match {
    case Some( ( v: FOLVar, formula: FOLFormula ) ) => Some( ( v, formula ) )
    case _ => None
  }

  object Block {
    def apply( vars: Seq[Var], formula: Expr ): Expr = vars match {
      case v +: vs => QuantifierHelper.this( v, apply( vs, formula ) )
      case Seq()   => formula
    }
    def apply( vars: Seq[Var], formula: Formula ): Formula =
      apply( vars, formula.asInstanceOf[Expr] ).asInstanceOf[Formula]
    def apply( vars: Seq[FOLVar], formula: FOLFormula ): FOLFormula =
      apply( vars, formula.asInstanceOf[Expr] ).asInstanceOf[FOLFormula]

    private object SingleQ {
      def unapply( e: Expr ) = QuantifierHelper.this.unapply( e )
    }
    def unapply( e: Expr ): Some[( List[Var], Expr )] = e match {
      case SingleQ( v, Block( vs, f ) ) => Some( ( v :: vs, f ) )
      case _                            => Some( ( List(), e ) )
    }
    def unapply( f: Formula ): Some[( List[Var], Formula )] =
      unapply( f.asInstanceOf[Expr] ).asInstanceOf[Some[( List[Var], Formula )]]
    def unapply( f: FOLFormula ): Some[( List[FOLVar], FOLFormula )] =
      unapply( f.asInstanceOf[Expr] ).asInstanceOf[Some[( List[FOLVar], FOLFormula )]]
  }
}

object All extends QuantifierHelper( ForallC )
object Ex extends QuantifierHelper( ExistsC )

object Quant {
  def apply( x: Var, sub: Formula, pol: Boolean ): Formula =
    if ( pol ) All( x, sub ) else Ex( x, sub )

  def unapply( f: Formula ): Option[( Var, Formula, Boolean )] =
    f match {
      case All( v, g ) => Some( ( v, g, true ) )
      case Ex( v, g )  => Some( ( v, g, false ) )
      case _           => None
    }
}

class BinaryPropConnectiveHelper( val c: MonomorphicLogicalC ) {
  def apply( a: Expr, b: Expr ): Formula =
    Apps( c(), a, b ).asInstanceOf[Formula]
  def apply( a: FOLFormula, b: FOLFormula ): FOLFormula =
    apply( a, b.asInstanceOf[Expr] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula, b: PropFormula ): PropFormula =
    apply( a, b.asInstanceOf[Expr] ).asInstanceOf[PropFormula]

  def unapply( formula: Expr ): Option[( Formula, Formula )] = formula match {
    case App( App( c(), a: Formula ), b: Formula ) => Some( ( a, b ) )
    case _                                         => None
  }
  def unapply( formula: FOLFormula ): Option[( FOLFormula, FOLFormula )] =
    unapply( formula.asInstanceOf[FOLExpression] )
  def unapply( formula: FOLExpression ): Option[( FOLFormula, FOLFormula )] =
    unapply( formula.asInstanceOf[Expr] ) match {
      case Some( ( a: FOLFormula, b: FOLFormula ) ) => Some( ( a, b ) )
      case _                                        => None
    }
  def unapply( formula: PropFormula ): Option[( PropFormula, PropFormula )] =
    unapply( formula.asInstanceOf[Expr] ) match {
      case Some( ( a: PropFormula, b: PropFormula ) ) => Some( ( a, b ) )
      case _ => None
    }
}

class MonoidalBinaryPropConnectiveHelper( c: MonomorphicLogicalC, val neutral: MonomorphicLogicalC ) extends BinaryPropConnectiveHelper( c ) {
  def apply( fs: TraversableOnce[Expr] ): Formula = nAry( fs.toSeq: _* )
  def apply( fs: TraversableOnce[FOLFormula] )( implicit d: DummyImplicit ): FOLFormula = nAry( fs.toSeq: _* )

  def leftAssociative( fs: Expr* ): Formula =
    fs.reduceLeftOption( super.apply ).getOrElse( neutral() ).asInstanceOf[Formula]
  def leftAssociative( fs: FOLFormula* ): FOLFormula =
    leftAssociative( fs.asInstanceOf[Seq[Expr]]: _* ).asInstanceOf[FOLFormula]

  def rightAssociative( fs: Expr* ): Formula =
    fs.reduceRightOption( super.apply ).getOrElse( neutral() ).asInstanceOf[Formula]
  def rightAssociative( fs: FOLFormula* ): FOLFormula =
    rightAssociative( fs.asInstanceOf[Seq[Expr]]: _* ).asInstanceOf[FOLFormula]

  object nAry {
    def apply( fs: Expr* )( implicit d: DummyImplicit ): Formula = leftAssociative( fs: _* )
    def apply( fs: FOLFormula* )( implicit d: DummyImplicit ): FOLFormula = leftAssociative( fs: _* )

    private object Binary {
      def unapply( formula: Expr ) = MonoidalBinaryPropConnectiveHelper.this.unapply( formula )
    }

    def unapply( formula: Formula ): Some[List[Formula]] = formula match {
      case Binary( nAry( as ), nAry( bs ) ) => Some( as ::: bs )
      case neutral()                        => Some( List() )
      case _                                => Some( List( formula ) )
    }

    def unapply( formula: FOLFormula ): Some[List[FOLFormula]] =
      unapply( formula.asInstanceOf[Formula] ).asInstanceOf[Some[List[FOLFormula]]]
  }
}

object And extends MonoidalBinaryPropConnectiveHelper( AndC, TopC )
object Or extends MonoidalBinaryPropConnectiveHelper( OrC, BottomC )
object Imp extends BinaryPropConnectiveHelper( ImpC ) {
  object Block {
    def apply( as: Seq[Formula], b: Formula ): Formula = as.foldRight( b )( Imp( _, _ ) )
    def unapply( f: Formula ): Some[( List[Formula], Formula )] = f match {
      case Imp( a, Block( as, b ) ) => Some( ( a :: as, b ) )
      case b                        => Some( ( Nil, b ) )
    }
  }
}

class UnaryPropConnectiveHelper( val c: MonomorphicLogicalC ) {
  def apply( a: Expr ): Formula = Apps( c(), a ).asInstanceOf[Formula]
  def apply( a: FOLFormula ): FOLFormula = apply( a.asInstanceOf[Expr] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula ): PropFormula = apply( a.asInstanceOf[Expr] ).asInstanceOf[PropFormula]

  def unapply( formula: Expr ): Option[Formula] = formula match {
    case App( c(), a: Formula ) => Some( a )
    case _                      => None
  }
  def unapply( formula: FOLFormula ): Option[FOLFormula] =
    unapply( formula.asInstanceOf[FOLExpression] )
  def unapply( formula: FOLExpression ): Option[FOLFormula] =
    unapply( formula.asInstanceOf[Expr] ) match {
      case Some( a: FOLFormula ) => Some( a )
      case _                     => None
    }
  def unapply( formula: PropFormula ): Option[PropFormula] =
    unapply( formula.asInstanceOf[Expr] ) match {
      case Some( a: PropFormula ) => Some( a )
      case _                      => None
    }
}

object Neg extends UnaryPropConnectiveHelper( NegC )

class NullaryPropConnectiveHelper( val c: MonomorphicLogicalC ) {
  def apply(): PropFormula with Const = c().asInstanceOf[PropFormula with Const]
  def unapply( formula: PropFormula ) = c() == formula
}

object Top extends NullaryPropConnectiveHelper( TopC )
object Bottom extends NullaryPropConnectiveHelper( BottomC )

object Eq {
  def apply( a: Expr, b: Expr ): Atom = Apps( EqC( a.ty ), a, b ).asInstanceOf[Atom]
  def apply( a: FOLTerm, b: FOLTerm ): FOLAtom =
    apply( a, b.asInstanceOf[Expr] ).asInstanceOf[FOLAtom]

  def unapply( e: Expr ): Option[( Expr, Expr )] = e match {
    case App( App( EqC( _ ), a ), b ) => Some( a, b )
    case _                            => None
  }
  def unapply( f: FOLFormula ): Option[( FOLTerm, FOLTerm )] = unapply( f.asInstanceOf[FOLExpression] )
  def unapply( f: FOLExpression ): Option[( FOLTerm, FOLTerm )] = f.asInstanceOf[Expr] match {
    case Eq( a: FOLTerm, b: FOLTerm ) => Some( a, b )
    case _                            => None
  }
}
