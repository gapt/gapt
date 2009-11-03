/*
 * Symbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

object Symbols {

    abstract class SymbolA

    abstract class VariableSymbolA extends SymbolA

    trait StringSymbol extends SymbolA {
        val string: String
        override def equals(a: Any) = a match {
            case s: StringSymbol => (s.string == string)
            case _ => false
        }
        override def hashCode() = string.hashCode
        override def toString() = string
    }

    trait LatexSymbol extends SymbolA {
        val latexCommand: String
    }

    object SymbolImplicitConverters {
        implicit def stringToVariableSymbol(s: String): VariableSymbolA = new VariableSymbolA with StringSymbol {val string = s}
        implicit def toString(symbol: StringSymbol) = symbol.string
    }
}
