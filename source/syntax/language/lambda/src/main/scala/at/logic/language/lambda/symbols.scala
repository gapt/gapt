/*
 * Symbols.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import at.logic.utils.ds.streams.Definitions._

package symbols {

  abstract class SymbolA extends Ordered[SymbolA] {
    override def equals(a: Any) = a match {
      case s1: SymbolA => unique == s1.unique && toString == s1.toString
      case _ => false
    }
    protected def unique: String // used to allow equality to work properly even for anonymous classes
    override def toString() = unique

    // this function outputs the string which creates
    // an object like this. can be used to create
    // tests based on bugs.
    def toCode : String
  }

  abstract class VariableSymbolA extends SymbolA { 
    def unique = "VariableSymbolA" 
  }

  trait StringSymbol extends SymbolA {
    val string: String
    override def hashCode() = string.hashCode
    override def toString() = string

    // for trait Ordered
    def compare(that: SymbolA) = that match {
      case StringSymbol( s ) => string.compare( s )
    }
  }

  object StringSymbol {
    def unapply( s: SymbolA ) = s match {
      case ss : StringSymbol => Some( ss.string )
      case _ => None
    }
  }

  case class VariableStringSymbol( val string : String ) extends VariableSymbolA with StringSymbol
  {
    def toCode = "VariableStringSymbol( \"" + string + "\" )"
  }

  trait LatexSymbol extends SymbolA {
    val latexCommand: String
  }

  object ImplicitConverters {
    implicit def stringToVariableSymbol(s: String): VariableSymbolA = VariableStringSymbol(s)
    implicit def toString(symbol: StringSymbol) = symbol.string
  }

  // TODO: need a way to take the context into account!
  //
  // For now: whenever Vars are created, tell the factory about it.
  // It keeps a set of the vars, and makes sure it never returns them.
  // 
  // In the future: find a more efficient way that does this in constant
  // time. Tomer suggests eg. to compute a value for every created Var,
  // and to return something that has a bigger value.
  //
  object FreshVariableSymbolFactory {
    private def variable_symbol_stream_from(n: Int): Stream[VariableStringSymbol] =
      Stream.cons(new VariableStringSymbol( "x_{" + n + "}" ), variable_symbol_stream_from( n + 1 ) )

    private var variable_symbol_stream = variable_symbol_stream_from( 0 )

    // This method resets the internal state of the factory.
    // WARNING: uniqueness of variable symbols is now not guaranteed anymore
    // (since variable symbols returned before the reset call may now
    // be returned again)
    //
    // Hence, this function should only be used for testing.

    def reset = { variable_symbol_stream = variable_symbol_stream_from( 0 ) }

    def getVariableSymbols = {
      val stream = even( variable_symbol_stream )
      variable_symbol_stream = odd( variable_symbol_stream )
      stream
    }

    def getVariableSymbol = {
      val sym = variable_symbol_stream.head
      variable_symbol_stream = variable_symbol_stream.tail
      sym
    }
  }
}
