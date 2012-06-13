package at.logic.language.schemata
import at.logic.language.hol.logicSymbols._
//import

package logicSymbols {


  case object BigAndSymbol extends LogicalSymbolsA {
    override def unique = "BigAndSymbol"
    override def toString = "⋀"
    def toCode = "BigAndSymbol"
  }

  case object BigOrSymbol extends LogicalSymbolsA {
    override def unique = "BigOrSymbol"
    override def toString = "⋁"
    def toCode = "BigOrSymbol"
  }

  case object PlusSymbol extends LogicalSymbolsA {
    override def unique = "Plus"
    override def toString = "+"
    def toCode = "Plus"
  }

  case object TimesSymbol extends LogicalSymbolsA {
    override def unique = "Times"
    override def toString = "×"
    def toCode = "Times"
  }
}