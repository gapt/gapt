/*
 * Symbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

package symbols {

  abstract class SymbolA {
    override def equals(a: Any) = a match {
      case s1: SymbolA => unique == s1.unique && toString == s1.toString
      case _ => false
    }
    protected def unique: String // used to allow equality to work properly even for anonymous classes
    override def toString() = unique
  }

  abstract class VariableSymbolA extends SymbolA { def unique = "VariableSymbolA"}

  trait StringSymbol extends SymbolA {
    val string: String
    override def hashCode() = string.hashCode
    override def toString() = string
  }

  case class VariableStringSymbol( val string : String ) extends VariableSymbolA with StringSymbol

  trait LatexSymbol extends SymbolA {
    val latexCommand: String
  }

  object ImplicitConverters {
    implicit def stringToVariableSymbol(s: String): VariableSymbolA = VariableStringSymbol(s)
    implicit def toString(symbol: StringSymbol) = symbol.string
  }
}
