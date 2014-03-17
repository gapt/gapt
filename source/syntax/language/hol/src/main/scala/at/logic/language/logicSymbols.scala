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
  abstract class LogicalSymbolsA extends ConstantSymbolA {
    def unique : String

     // for trait Ordered
    def compare(that: SymbolA) = that match {
      case LogicalSymbolsA( s ) => unique.compare( s )
    }
  }

  case object EqSymbol extends ConstantSymbolA {
    override def unique = "EqSymbol"
    override def toString = "="
    def toCode = "EqSymbol"
    def compare(that: SymbolA) = that match {
      case a: ConstantSymbolA => unique.compare( a.unique )
    }
  }

  object LogicalSymbolsA {def unapply(s: SymbolA): Option[String] = s match {case ls: LogicalSymbolsA => Some(ls.unique); case _ => None}}

  case object NegSymbol extends LogicalSymbolsA {
    override def unique = "NegSymbol"
    override def toString = "¬"
    def toCode = "NegSymbol"
  }

  case object AndSymbol extends LogicalSymbolsA {
    override def unique = "AndSymbol"
    override def toString = "∧"
    def toCode = "AndSymbol"
  }

  case object OrSymbol extends LogicalSymbolsA {
    override def unique = "OrSymbol"
    override def toString = "∨"
    def toCode = "OrSymbol"
  }

  case object ImpSymbol extends LogicalSymbolsA {
    override def unique = "ImpSymbol"
    override def toString = "⊃"
    def toCode = "ImpSymbol"
  }

  case object ExistsSymbol extends LogicalSymbolsA {
    override def unique = "ExistsSymbol"
    override def toString = "∃"
    def toCode = "ExistsSymbol"
  }

  case object ForallSymbol extends LogicalSymbolsA {
    override def unique = "ForallSymbol"
    override def toString = "∀"
    def toCode = "ForallSymbol"
  }

  case object BottomSymbol extends LogicalSymbolsA {
    override def unique = "BottomSymbol"
    override def toString = "⊥"
    def toCode = "BottomSymbol"
  }

  case object TopSymbol extends LogicalSymbolsA {
    override def unique = "TopSymbol"
    override def toString = "⊤"
    def toCode = "TopSymbol"
  }

  case class ConstantStringSymbol( val string : String ) extends ConstantSymbolA with StringSymbol
  {
    def toCode = "ConstantStringSymbol( \"" + string + "\" )"
  }

  object ImplicitConverters {
    implicit def stringToVarConstSymbol(s: String): SymbolA = {
      val chr = s.charAt(0)
      if (chr.isUpper || chr.equals('a') || chr.equals('b') || chr.equals('c')) new ConstantStringSymbol( s )
      else new VariableStringSymbol( s )
    }
  }
}
