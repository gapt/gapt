package gapt.expr.formula

import gapt.expr.Expr
import gapt.expr.formula.constants.MonomorphicLogicalC
import gapt.expr.formula.fol.FOLFormula

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
