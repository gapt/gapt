package gapt.formats.tip.transformation

import gapt.formats.tip.parser.TipSmtProblem

trait TipSmtProblemTransformation {

  def transform( problem: TipSmtProblem ): TipSmtProblem

  def ->>:( other: TipSmtProblemTransformation ): TipSmtProblemTransformation = {
    new TipSmtProblemTransformation {
      override def transform( problem: TipSmtProblem ): TipSmtProblem =
        TipSmtProblemTransformation.this.transform( other.transform( problem ) )
    }
  }

  def >>:( problem: TipSmtProblem ): TipSmtProblem = transform( problem )
}
