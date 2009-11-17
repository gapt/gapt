/*
 * abstractTypedLambdaCalculus.scala
 *
 */

package at.logic.language.lambda

import scala.util.parsing.combinator._

object Types {
    abstract class TA {
        def ->(that:TA) = new ->(this, that)
    }
    abstract class TAtomicA extends TA
    abstract class TComplexA extends TA
    case class Ti() extends TAtomicA ; def i = Ti()
    case class To() extends TAtomicA ; def o = To()
    case class ->(in:TA, out:TA) extends TComplexA

    // convenience factory to create function types
    // with argument types from and return type to
    object FunctionType {
      def apply(to: TA, from: List[TA]) : TA = if (!from.isEmpty) (from :\ to)(->) else to
    }

    object  StringExtractor {
        def apply(t:TA):String = t match {
            case Ti() => "i"
            case To() => "o"
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

    object TAImplicitConverters {
        implicit def fromString(s:String):TA = StringExtractor.unapply(s) match {
            case Some(result) => result
            case None =>  throw new IllegalArgumentException("Bad syntax for types: "+s)
        }
    }

    trait Parsers extends JavaTokenParsers {
        def Type: Parser[TA] = (arrowType | iType | oType)
        def iType: Parser[TA] = "i" ^^ {x => Ti()}
        def oType: Parser[TA] = "o" ^^ {x => To()}
        def arrowType: Parser[TA] = "("~> Type~"->"~Type <~")" ^^ {case in ~ "->" ~ out => ->(in,out)}
    }

    class TypeException(s: String) extends Exception
}
