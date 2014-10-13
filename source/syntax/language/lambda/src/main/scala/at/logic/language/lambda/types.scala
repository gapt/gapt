/*
 * types.scala
 *
 */

package at.logic.language.lambda.types

import scala.util.parsing.combinator._

abstract class TA {
  def ->(that: TA) = new ->(this, that)
}
abstract class TAtomicA extends TA
abstract class TComplexA extends TA
object TAtomicA {
  def unapply(ta: TA) = ta match {
    case Tindex => Some(ta)
    case Ti => Some(ta)
    case To => Some(ta)
    case _ => None
  }
}

case object Tindex extends TAtomicA {override def toString = "ω"} // for indexed propositions in schema
case object Ti extends TAtomicA {override def toString = "ι"}
case object To extends TAtomicA {override def toString = "ο"}

case class ->(val in: TA, val out: TA) extends TComplexA {
  override def toString = "(" + in.toString + "->" + out.toString + ")"
}
// Overloading the apply method so that it takes strings.
object -> {
  def apply(in: String, out: String) = new ->(Type(in), Type(out))
  def apply(in: TA, out: String) = new ->(in, Type(out))
  def apply(in: String, out: TA) = new ->(Type(in), out)
  def unapply(ta: TA) = ta match {
    case t: -> => Some((t.in, t.out))
    case _ => None
  }
}

// convenience function to create function types
// with argument types from and return type to
object FunctionType {
  def apply(to: TA, from: List[TA]) : TA = if (!from.isEmpty) from.foldRight(to)((t, acc) => ->(t, acc)) else to
  def unapply(ta: TA): Option[Tuple2[TA, List[TA]]] = ta match {
    case TAtomicA(_) => Some(ta, Nil)
    case ->(t1, TAtomicA(t2)) => Some(t2, t1::Nil)
    case ->(t1, t2) => {
      unapply(t2) match {
        case Some((ta, ls)) => Some(ta, t1::ls)
        case None => None
      }
    }
    case _ => None
  }
}
  //gives the arity of a function - simple types have arity 0, complex types have 1 + arity of return value (because
  // of currying)
object Arity {
  def apply(t:TA) : Int = t match {
    case t1 -> t2 => 1 + Arity(t2)
    case _ => 0
  }
}

object  StringExtractor {
  def apply(t:TA):String = t match {
    case Ti => "i"
    case To => "o"
    case ->(in,out) => "("+ apply(in) + " -> " + apply(out) +")"
  }
  def unapply(s:String):Option[TA] = {
    val p = new JavaTokenParsers with Parsers
    p.parseAll(p.Type,s) match {
      case p.Success(result,_) => Some(result)
      case _ => None
    }
  }
}

object Type {
  def apply(s: String) : TA = StringExtractor.unapply(s) match {
    case Some(result) => result
    case None =>  throw new IllegalArgumentException("Bad syntax for types: "+s)
  }
}

trait Parsers extends JavaTokenParsers {
  def Type: Parser[TA] = (arrowType | iType | oType)
  def iType: Parser[TA] = "i" ^^ {x => Ti}
  def oType: Parser[TA] = "o" ^^ {x => To}
  def indexType: Parser[TA] = "e" ^^ {x => Tindex}
  def arrowType: Parser[TA] = "("~> Type~"->"~Type <~")" ^^ {case in ~ "->" ~ out => ->(in,out)}
}

class TypeException(s: String) extends Exception
