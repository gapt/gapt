/*
 * Symbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

object Symbols {

    abstract class SymbolA

    case class StringSymbol(string: String) extends SymbolA {
        override def toString = string
    }

    case class LatexSymbol(latexCommand: String, override val string: String) extends StringSymbol(string)

    object StringSymbolImplicitConverters {
        implicit def fromString(s: String) = StringSymbol(s)
    }

    object LatexSymbolImplicitConverters {
        implicit def toLatexSymbol(s: String) = LatexSymbol(s,s)
    }
}
