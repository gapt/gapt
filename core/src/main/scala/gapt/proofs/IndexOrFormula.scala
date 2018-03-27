package gapt.proofs

import gapt.expr.Formula

sealed trait IndexOrFormula {
  def getFormula( sequent: HOLSequent ): Formula
}

object IndexOrFormula {
  case class IsIndex( index: SequentIndex ) extends IndexOrFormula {
    def getFormula( sequent: HOLSequent ): Formula = sequent( index )
  }
  case class IsFormula( formula: Formula ) extends IndexOrFormula {
    def getFormula( sequent: HOLSequent ): Formula = formula
  }

  implicit def ofIndex( index: SequentIndex ): IndexOrFormula = IsIndex( index )
  implicit def ofFormula( formula: Formula ): IndexOrFormula = IsFormula( formula )
}
