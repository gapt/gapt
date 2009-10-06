/*
 * abstractTypedLambdaCalculus.scala
 *
 */

package at.logic.language


object Types {
    abstract class TA {
        def ->(that:TA) = new ->(this, that)
    }
    abstract class TAtomicA extends TA
    abstract class TComplexA extends TA
    case class Ti() extends TAtomicA ; def i = Ti()
    case class To() extends TAtomicA ; def o = To()
    case class ->(in:TA, out:TA) extends TComplexA

    object  TypesToStringExtractor {
        def apply(t:TA):String = t match {
            case Ti() => "i"
            case To() => "o"
            case ->(in,out) => "("+ apply(in) + " -> " + apply(out) +")"
        }
        def unapply(s:String):Option[TA] = Parsers.parseAll(Parsers.Type,s) match {
            case Parsers.Success(result,_) => Some(result)
            case _ => None
        }
    }

    object TAImplicitConverters {
        implicit def toTA(s:String):TA = TypesToStringExtractor.unapply(s) match {
            case Some(result) => result
            case None =>  throw new IllegalArgumentException("Bad syntax for types: "+s)
        }
    }

    import scala.util.parsing.combinator._
    object Parsers extends JavaTokenParsers {
        def Type: Parser[TA] = (arrowType | iType | oType)
        def iType: Parser[TA] = "i" ^^ {x => Ti()}
        def oType: Parser[TA] = "o" ^^ {x => To()}
        def arrowType: Parser[TA] = "("~> Type~"->"~Type <~")" ^^ {case in ~ "->" ~ out => ->(in,out)}
    }
}