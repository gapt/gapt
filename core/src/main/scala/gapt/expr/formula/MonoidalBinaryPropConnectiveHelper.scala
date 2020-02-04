package gapt.expr.formula

import gapt.expr.Expr
import gapt.expr.formula.constants.MonomorphicLogicalC
import gapt.expr.formula.fol.FOLFormula

class MonoidalBinaryPropConnectiveHelper( c: MonomorphicLogicalC, val neutral: MonomorphicLogicalC ) extends BinaryPropConnectiveHelper( c ) {
  def apply( fs: IterableOnce[Expr] ): Formula = nAry( fs.iterator.to( Seq ): _* )
  def apply( fs: IterableOnce[FOLFormula] )( implicit d: DummyImplicit ): FOLFormula = nAry( fs.iterator.to( Seq ): _* )

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
      def unapply( formula: Expr ): Option[( Formula, Formula )] = MonoidalBinaryPropConnectiveHelper.this.unapply( formula )
    }

    def unapply( formula: Formula ): Some[List[Formula]] = formula match {
      case Binary( nAry( as ), nAry( bs ) ) => Some( as ::: bs )
      case _                                => Some( List( formula ) )
    }

    def unapply( formula: FOLFormula ): Some[List[FOLFormula]] =
      unapply( formula.asInstanceOf[Formula] ).asInstanceOf[Some[List[FOLFormula]]]
  }
}
