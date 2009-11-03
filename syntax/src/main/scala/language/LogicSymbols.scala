/*
 * LogicSymbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import Symbols._

object LogicSymbols {
    abstract class ConstantSymbolA extends SymbolA

    case object NegSymbol extends ConstantSymbolA
    case object AndSymbol extends ConstantSymbolA
    case object OrSymbol extends ConstantSymbolA
    case object ImpSymbol extends ConstantSymbolA
    case object ExistsSymbol extends ConstantSymbolA
    case object ForallSymbol extends ConstantSymbolA

    object LogicSymbolsImplicitConverters {

        implicit def stringToConstantSymbol(s: String): ConstantSymbolA = new ConstantSymbolA with StringSymbol {val string = s}
    }
}
