
package at.logic.gapt.expr.schema.logicSymbols

import at.logic.gapt.expr._

case object BigAndSymbol extends SymbolA {
  def unique = "BigAndSymbol"
  override def toString = "⋀"
  def toCode = "BigAndSymbol"
}

case object BigOrSymbol extends SymbolA {
  def unique = "BigOrSymbol"
  override def toString = "⋁"
  def toCode = "BigOrSymbol"
}

case object PlusSymbol extends SymbolA {
  def unique = "Plus"
  override def toString = "+"
  def toCode = "Plus"
}

case object TimesSymbol extends SymbolA {
  def unique = "Times"
  override def toString = "×"
  def toCode = "Times"
}

// Helpers to represent preconditions in construction of characteristic clause set
case object BiggerThanSymbol extends SymbolA {
  def unique = "BiggerThanSymbol"
  override def toString = ">"
  def toCode = "BiggerThanSymbol"

  /*def compare(that: SymbolA) = that match {
    case a: ConstantSymbolA => unique.compare( a.unique )
  }*/
}

case object simSymbol extends SymbolA {
  def unique = "simSymbol"
  override def toString = "~"
  def toCode = "simSymbol"
  /* def compare(that: SymbolA) = that match {
  case a: SymbolA => unique.compare( a.unique )
}*/
}

case object LessThanSymbol extends SymbolA {
  def unique = "LessThanSymbol"
  override def toString = "<"
  def toCode = "LessThanSymbol"
  /*
  def compare(that: SymbolA) = that match {
    case a: ConstantSymbolA => unique.compare( a.unique )
  }*/
}

case object LeqSymbol extends SymbolA {
  def unique = "LeqSymbol"
  override def toString = "≤"
  def toCode = "LeqSymbol"
  /*
  def compare(that: SymbolA) = that match {
    case a: ConstantSymbolA => unique.compare( a.unique )
  }*/
}
