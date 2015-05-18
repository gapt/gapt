package at.logic.gapt.expr

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap

trait HOLFormula extends LambdaExpression

trait LogicalConstant extends Const

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
trait FOLFormula extends FOLLambdaTerm with HOLFormula with FOLExpression {
  private[expr] override val returnType = To
  private[expr] override val numberOfArguments = 0

  override def renameSymbols( map: SymbolMap ): FOLFormula = NameReplacement( this, map )
}
private[expr] trait FOLFormulaWithBoundVar extends LambdaExpression
trait FOLQuantifier extends LogicalConstant

private[expr] trait PropLambdaTerm extends FOLLambdaTerm {
  private[expr] override val returnType = To
}
trait PropFormula extends PropLambdaTerm with FOLFormula
trait PropConnective extends LogicalConstant with PropLambdaTerm {
  private[expr] override val returnType = To
}
trait PropAtom extends Const with PropFormula

private[expr] object determineTraits {
  def forVar( sym: SymbolA, exptype: TA ): Var = exptype match {
    case Ti => new Var( sym, exptype ) with FOLVar
    case To => new Var( sym, exptype ) with HOLFormula
    case _  => new Var( sym, exptype )
  }
  def forConst( sym: SymbolA, exptype: TA ): Const = ( sym, exptype ) match {
    case ForallC( Ti ) | ExistsC( Ti ) => new Const( sym, exptype ) with FOLQuantifier
    case AndC() | OrC() | ImpC() => new Const( sym, exptype ) with PropConnective {
      override val numberOfArguments = 2
    }
    case NegC() => new Const( sym, exptype ) with PropConnective {
      override val numberOfArguments = 1
    }
    case TopC() | BottomC() => new Const( sym, exptype ) with PropConnective with PropFormula
    case ( _, Ti )          => new Const( sym, exptype ) with FOLConst
    case ( _, To )          => new Const( sym, exptype ) with PropFormula
    case ( _, FOLHeadType( Ti, n ) ) => new Const( sym, exptype ) with FOLLambdaTerm {
      override val returnType = Ti
      override val numberOfArguments = n
    }
    case ( _, FOLHeadType( To, n ) ) => new Const( sym, exptype ) with PropLambdaTerm {
      override val numberOfArguments = n
    }
    case _ => new Const( sym, exptype )
  }
  def forApp( f: LambdaExpression, a: LambdaExpression ): App = ( f, a ) match {
    case ( f: PropLambdaTerm, a: PropFormula ) => f.numberOfArguments match {
      case 1 => new App( f, a ) with PropFormula
      case n => new App( f, a ) with PropLambdaTerm {
        override val numberOfArguments = n - 1
      }
    }
    case ( f: FOLLambdaTerm, a: FOLExpression ) => f.numberOfArguments match {
      case 1 => f.returnType match {
        case Ti => new App( f, a ) with FOLTerm
        case To => new App( f, a ) with FOLFormula
      }
      case n => new App( f, a ) with FOLLambdaTerm {
        override val numberOfArguments = n - 1
        override val returnType = f.returnType
      }
    }
    case ( f: FOLQuantifier, _ ) => a match {
      case a: FOLFormulaWithBoundVar => new App( f, a ) with FOLFormula
      case _                         => new App( f, a ) with HOLFormula
    }
    case _ => f.exptype match {
      case ->( _, To ) => new App( f, a ) with HOLFormula
      case _           => new App( f, a )
    }
  }
  def forAbs( v: Var, t: LambdaExpression ): Abs = ( v.exptype, t ) match {
    case ( Ti, t: FOLFormula ) => new Abs( v, t ) with FOLFormulaWithBoundVar
    case _                     => new Abs( v, t )
  }
}

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
