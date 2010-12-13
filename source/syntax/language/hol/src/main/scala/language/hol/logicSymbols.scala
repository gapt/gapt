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
  object LogicalSymbolsA {def unapply(s: SymbolA): Boolean = s match {case ls: LogicalSymbolsA => true; case _ => false}}
  case object NegSymbol extends LogicalSymbolsA {
    override def unique = "NegSymbol"
    override def toString = "¬"
  }
  case object AndSymbol extends LogicalSymbolsA {
    override def unique = "AndSymbol"
    override def toString = "∧"
  }
  case object OrSymbol extends LogicalSymbolsA {
    override def unique = "OrSymbol"
    override def toString = "∨"
  }
  case object ImpSymbol extends LogicalSymbolsA {
    override def unique = "ImpSymbol"
    override def toString = "⊃"
  }
  case object ExistsSymbol extends LogicalSymbolsA {
    override def unique = "ExistsSymbol"
    override def toString = "∃"
  }
  case object ForallSymbol extends LogicalSymbolsA {
    override def unique = "ForallSymbol"
    override def toString = "∀"
  }
  case object BottomSymbol extends LogicalSymbolsA {
    override def unique = "BottomSymbol"
    override def toString = "⊥"
  }

  case class ConstantStringSymbol( val string : String ) extends ConstantSymbolA with StringSymbol

  object ImplicitConverters {
    implicit def stringToVarConstSymbol(s: String): SymbolA = {
      val chr = s.charAt(0)
      if (chr.isUpper || chr.equals('a') || chr.equals('b') || chr.equals('c')) new ConstantStringSymbol( s )
      else new VariableStringSymbol( s )
    }
  }
}
