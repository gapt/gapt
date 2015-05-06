package at.logic.gapt.expr

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap
import types._

trait Formula extends LambdaExpression

trait DistinguishedConstant extends Const

trait FOLExpression extends LambdaExpression {
  def renameSymbols( map: SymbolMap ): FOLExpression = NameReplacement( this, map )
}
private[expr] trait FOLLambdaTerm extends LambdaExpression {
  private[expr] def returnType: TA
  private[expr] def numberOfArguments: Int
}
trait FOLTerm extends FOLLambdaTerm with FOLExpression {
  private[expr] override val returnType = Ti
  private[expr] override val numberOfArguments = 0

  override def renameSymbols( map: SymbolMap ): FOLTerm = NameReplacement( this, map ).asInstanceOf[FOLTerm]
}
trait FOLVar extends Var with FOLTerm
trait FOLConst extends Const with FOLTerm
trait FOLFormula extends FOLLambdaTerm with Formula with FOLExpression {
  private[expr] override val returnType = To
  private[expr] override val numberOfArguments = 0

  override def renameSymbols( map: SymbolMap ): FOLFormula = NameReplacement( this, map )
}
private[expr] trait FOLFormulaWithBoundVar extends LambdaExpression
trait FOLQuantifier extends DistinguishedConstant

private[expr] trait PropLambdaTerm extends FOLLambdaTerm {
  private[expr] override val returnType = To
}
trait PropFormula extends PropLambdaTerm with FOLFormula
trait PropConnective extends DistinguishedConstant with PropLambdaTerm {
  private[expr] override val returnType = To
}
trait PropAtom extends Const with PropFormula

object FOLVar {
  def apply( sym: String ): FOLVar = Var( sym, Ti ).asInstanceOf[FOLVar]
  def unapply( e: LambdaExpression ) = e match {
    case Var( sym, Ti ) => Some( sym )
    case _              => None
  }
}

object FOLConst {
  def apply( sym: String ): FOLConst = FOLFunction( sym ).asInstanceOf[FOLConst]
  def unapply( e: LambdaExpression ): Option[String] = e match {
    case FOLFunction( name, List() ) => Some( name )
    case _                           => None
  }
}

