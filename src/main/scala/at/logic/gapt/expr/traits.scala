package at.logic.gapt.expr
import types._

trait Formula extends LambdaExpression

trait DistinguishedConstant extends Const

trait SchematicLambdaTerm extends LambdaExpression {
  def returnType: TA
  def numberOfArguments: Int
}
trait SchematicTerm extends SchematicLambdaTerm {
  override val returnType = Ti
  override val numberOfArguments = 0
}
trait SchematicIntTerm extends SchematicLambdaTerm {
  override val returnType = Tindex
  override val numberOfArguments = 0
}
trait SchematicVar extends Var with SchematicIntTerm
trait SchematicFormula extends SchematicLambdaTerm with Formula {
  override val returnType = To
  override val numberOfArguments = 0
}
trait SchematicFormulaWithBoundVar extends SchematicLambdaTerm {
  override val returnType = Ti
  override val numberOfArguments = 1
}
trait SchematicFormulaWithBoundIndex extends SchematicLambdaTerm {
  override val returnType = Tindex
  override val numberOfArguments = 1
}
trait SchematicBigConnective extends DistinguishedConstant

trait FOLLambdaTerm extends LambdaExpression with SchematicLambdaTerm
trait FOLTerm extends FOLLambdaTerm with SchematicTerm
trait FOLVar extends Var with FOLTerm
trait FOLFormula extends FOLLambdaTerm with SchematicFormula
trait FOLFormulaWithBoundVar extends SchematicFormulaWithBoundVar
trait FOLQuantifier extends DistinguishedConstant

trait PropLambdaTerm extends FOLLambdaTerm {
  override val returnType = To
}
trait PropFormula extends PropLambdaTerm with FOLFormula {
  override val numberOfArguments = 0
}
trait PropConnective extends DistinguishedConstant with PropLambdaTerm {
  override val returnType = To
}
trait PropAtom extends Const with PropFormula

object FOLVar {
  def apply( sym: String ): FOLVar = Var( sym, Ti ).asInstanceOf[FOLVar]
  def unapply( e: LambdaExpression ) = e match {
    case Var( sym, Ti ) => Some( sym )
    case _              => None
  }
}
