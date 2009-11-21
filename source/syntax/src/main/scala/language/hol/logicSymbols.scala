/*
 * LogicSymbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import at.logic.language.lambda.symbols._

package logicSymbols {
  abstract class ConstantSymbolA extends SymbolA { def unique = "ConstantSymbolA"}
  abstract class LogicalSymbolsA extends ConstantSymbolA
  case object NegSymbol extends LogicalSymbolsA { override def unique = "NegSymbol"}
  case object AndSymbol extends LogicalSymbolsA { override def unique = "AndSymbol"}
  case object OrSymbol extends LogicalSymbolsA { override def unique = "OrSymbol"}
  case object ImpSymbol extends LogicalSymbolsA { override def unique = "ImpSymbol"}
  case object ExistsSymbol extends LogicalSymbolsA { override def unique = "ExistsSymbol"}
  case object ForallSymbol extends LogicalSymbolsA { override def unique = "ForallSymbol"}

  class ConstantStringSymbol( val string : String ) extends ConstantSymbolA with StringSymbol

  object ImplicitConverters {
    implicit def stringToVarConstSymbol(s: String): SymbolA = {
      val chr = s.charAt(0)
      if (chr.isUpperCase || chr.equals('a') || chr.equals('b') || chr.equals('c')) new ConstantStringSymbol( s )
      else new VariableStringSymbol( s )
    }
  }
}
