/*
 * LogicSymbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import at.logic.language.lambda.Symbols._

object LogicSymbols {
    abstract class ConstantSymbolA extends SymbolA

    case object NegSymbol extends ConstantSymbolA
    case object AndSymbol extends ConstantSymbolA
    case object OrSymbol extends ConstantSymbolA
    case object ImpSymbol extends ConstantSymbolA
    case object ExistsSymbol extends ConstantSymbolA
    case object ForallSymbol extends ConstantSymbolA

    class ConstantStringSymbol( val string : String ) extends ConstantSymbolA with StringSymbol
    class VariableStringSymbol( val string : String ) extends VariableSymbolA with StringSymbol

    object LogicSymbolsDefaultConverters {

        implicit def stringToVarConstSymbol(s: String): SymbolA = {
            val chr = s.charAt(0)
            if (chr.isUpperCase || chr.equals('a') || chr.equals('b') || chr.equals('c')) new ConstantStringSymbol( s )
            else new VariableStringSymbol( s )
        }
    }
}
