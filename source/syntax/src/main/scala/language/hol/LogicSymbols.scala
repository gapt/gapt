/*
 * LogicSymbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import at.logic.language.lambda.Symbols._

object LogicSymbols {
    abstract class ConstantSymbolA extends SymbolA { def unique = "ConstantSymbolA"}

    case object NegSymbol extends ConstantSymbolA { override def unique = "NegSymbol"}
    case object AndSymbol extends ConstantSymbolA { override def unique = "AndSymbol"}
    case object OrSymbol extends ConstantSymbolA { override def unique = "OrSymbol"}
    case object ImpSymbol extends ConstantSymbolA { override def unique = "ImpSymbol"}
    case object ExistsSymbol extends ConstantSymbolA { override def unique = "ExistsSymbol"}
    case object ForallSymbol extends ConstantSymbolA { override def unique = "ForallSymbol"}

    class ConstantStringSymbol( val string : String ) extends ConstantSymbolA with StringSymbol

    object LogicSymbolsDefaultConverters {

        implicit def stringToVarConstSymbol(s: String): SymbolA = {
            val chr = s.charAt(0)
            if (chr.isUpperCase || chr.equals('a') || chr.equals('b') || chr.equals('c')) new ConstantStringSymbol( s )
            else new VariableStringSymbol( s )
        }
    }
}
