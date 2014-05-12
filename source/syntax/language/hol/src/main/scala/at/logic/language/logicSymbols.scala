/*
 * logicSymbols.scala
 *
 */

package at.logic.language.hol.logicSymbols

import at.logic.language.lambda.symbols._

abstract class LogicalSymbolA extends SymbolA {
  def unique : String
}
object LogicalSymbolA {
  def unapply(s: SymbolA): Option[String] = s match {
    case ls: LogicalSymbolA => Some(ls.unique); 
    case _ => None
  }
}

object EqSymbol extends SymbolA {
  def unique = "EqSymbol"
  override def toString = "="
  def toCode = "EqSymbol"
}

object NegSymbol extends LogicalSymbolA {
  override def unique = "NegSymbol"
  override def toString = "¬"
  def toCode = "NegSymbol"
}

object AndSymbol extends LogicalSymbolA {
  override def unique = "AndSymbol"
  override def toString = "∧"
  def toCode = "AndSymbol"
}

object OrSymbol extends LogicalSymbolA {
  override def unique = "OrSymbol"
  override def toString = "∨"
  def toCode = "OrSymbol"
}

object ImpSymbol extends LogicalSymbolA {
  override def unique = "ImpSymbol"
  override def toString = "⊃"
  def toCode = "ImpSymbol"
}

object ExistsSymbol extends LogicalSymbolA {
  override def unique = "ExistsSymbol"
  override def toString = "∃"
  def toCode = "ExistsSymbol"
}

object ForallSymbol extends LogicalSymbolA {
  override def unique = "ForallSymbol"
  override def toString = "∀"
  def toCode = "ForallSymbol"
}

object BottomSymbol extends LogicalSymbolA {
  override def unique = "BottomSymbol"
  override def toString = "⊥"
  def toCode = "BottomSymbol"
}

object TopSymbol extends LogicalSymbolA {
  override def unique = "TopSymbol"
  override def toString = "⊤"
  def toCode = "TopSymbol"
}

// Herbrand array
object HArraySymbol extends LogicalSymbolA {
  override def unique = "HArraySymbol"
  override def toString = "HA"
  def toCode = "HArraySymbol"
}

