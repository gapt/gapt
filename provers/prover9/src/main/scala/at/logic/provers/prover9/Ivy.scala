package at.logic.provers.prover9

import scala.util.parsing.combinator.{RegexParsers, JavaTokenParsers}
import scala.collection.immutable
import at.logic.provers.prover9.Lisp.SExpression
import java.io.{FileReader, FileInputStream}
import scala.util.parsing.input.{PagedSeqReader, StreamReader}
import scala.collection.immutable.PagedSeq

/**
 * Implements parsing of ivy format: https://www.cs.unm.edu/~mccune/papers/ivy/ . What is done here is a basic LISP
 * S-expression parser, without quote character, macros or other fancy stuff. Atoms have a reduced namespace and need to
 * be extended if necessary.
 *
 * Some remarks:
 * (1) regexp parsers eat whitespace and newlines
 * (2) recursive cases have to be put first
 */

/* Basic Lisp Datastructures: Atom, Cons and List -- be careful with namespace collisions in scala.*.List.
 * Printing a Datastructure should output valid Lisp.
 */
object Lisp {
  sealed class SExpression

  case class Atom(name : String) extends SExpression {
    override def toString = name
  }

  case class List(elements : immutable.List[SExpression] ) extends SExpression {
    def ::(head : SExpression) = Lisp.List(head::elements)
    def ++(list2 : Lisp.List) = Lisp.List(elements ++ list2.elements)

    def lst2string[T](fun:(T=>String), seperator: String, l:immutable.List[T]) : String = l match {
      case immutable.Nil => ""
      case immutable.List(x) => fun(x)
      case x :: xs => fun(x)  + seperator + lst2string(fun, seperator, xs)
    }

    override def toString = "("+ lst2string(((x:Any) => x.toString), " ", elements) + ")"
    //def prepend(head : SExpression, list : Lisp.List) = Lisp.List(head::list.list)
  }
  case class Cons(car: SExpression, cdr : SExpression) extends SExpression {
    override def toString = "( " + car + " . " + cdr + ")"
  }

}

/* Constructor object, takes a filename and tries to parse as a lisp_file  */
object Ivy {
  object IvyParser extends IvyParser {
    def apply(fn : String) : List[SExpression] = {
      val fis = new FileReader(fn)
      val pagedseq = new PagedSeq(fis.read)
      val reader = new PagedSeqReader(pagedseq)
      parseAll(lisp_file, reader) match {
        case Success(result, _) => result
        case NoSuccess(msg, _) =>
          throw new Exception("Ivy Parser Failed: "+msg)
      }
    }
  }

  /* The actual Parser, lexing and parsing is mixed which makes the grammar look a bit ugly sometimes */
  class IvyParser extends RegexParsers {
    def debug(s:String) = ()
    // --- parser transformers for putting elements into lists, concatenating parsing results, etc
    def wrap[T](s:T) = { debug("wrapping: '"+s+"'"); immutable.List(s) }
    def prepend[T](l : ~[T, immutable.List[T]]) : immutable.List[T] = { debug("prepending: '"+l+"'"); l match { case ~(l1,l2) => l1 :: l2  } }
    def prepend2[T](l : ~[~[T,T],immutable.List[T]]) : immutable.List[T] = { debug("prepending: '"+l+"'"); l match { case l1 ~ l2 ~ l3 => l1 :: l2 :: l3 } }
    def concat[T](l : ~[immutable.List[T],immutable.List[T]]) : immutable.List[T] = { debug("concatenating: '"+l+"'"); l match { case ~(l1,l2) => l1 ++ l2  } }

    def prepend_tolisplist(l : ~[SExpression, SExpression]) : Lisp.List = {
      l match { case ~(l1,Lisp.List(l2)) => Lisp.List(l1 :: l2)
                case _ => throw new Exception("Somethings wrong in the parser implementation!")
      }
    }
    def concat_lisplists(l : ~[SExpression,SExpression]) : Lisp.List = {
      l match { case ~(Lisp.List(l1),Lisp.List(l2)) => Lisp.List(l1 ++ l2)
                case _ => throw new Exception("Somethings wrong in the parser implementation!")
      }
    }

    def debugrule[T](t:T) : T = { println("dr: "+t.toString) ; t}

    def wrap_inlisplist(s:SExpression) = {  Lisp.List(s::Nil) }

    // ------------ start of grammar --------------------

    //def eof : Parser[String] = """\z""".r
    //def non_delimiter : Parser[String] = """[^,\(\)\[\]]([^,\.\(\)\[\]+])?""".r
    def comment : Parser[String] = """;;.*""".r
    def comments : Parser[String] = comment ~ comments ^^ ((x : ~[String,String]) => {val ~(s1,s2) = x; s1 + s2}) | comment

    //    def word : Parser[IvyToken] = """[^,\(\)\[\]\s]([^,\.\(\)\[\]\s]+)?""".r ^^ IvyToken
    //def word : Parser[IvyToken] = """[^,\.\(\)\[\]\s]*[^,\(\)\[\]\s][^,\.\(\)\[\]\s]*""".r ^^ IvyToken.apply
    //TODO: extend definition of word
    def word : Parser[SExpression] = """[a-zA-Z0-9=_+\-*/]+""".r ^^ Lisp.Atom   //contains only very restricted strings
    def string :Parser[SExpression] = """"[^"]*"""".r ^^ Lisp.Atom              //arbitrary strings wrapped in " "

    def atom : Parser[SExpression] = string | word

    def nil : Parser[SExpression] = (("(") ~> (")") | """[nN][iI][lL]""".r) ^^ ((x:Any) => Lisp.List(Nil)) //empty list

    def list : Parser[SExpression] = (nil | ("(") ~> list_ <~ (")"))            // arbitrary list
    def list_ : Parser[SExpression] =  ( (sexpression ^^ wrap_inlisplist) ~ list_ ) ^^ concat_lisplists |
                                       ( (sexpression ^^ wrap_inlisplist))

    // cons: cons'es are converted to lists if possible (second argument is a list)
    def cons : Parser[SExpression] = (("(") ~> sexpression) ~ (".") ~ (sexpression <~ (")")) ^^ (
      (exp: ~[~[SExpression, String], SExpression]) => {
        val car ~ _ ~ cdr = exp;
        cdr match {
          case Lisp.List(elems) => Lisp.List(car::elems)
          case _ => Lisp.Cons(car,cdr)
        }

      })

    //parsing of comments is a bit expensive :(
    def sexpression_ : Parser[SExpression] =  ( list | atom | cons)
    def sexpression : Parser[SExpression] =  opt(comments) ~> sexpression_ <~ opt(comments)

    //a file is a list of sexpressions
    def lisp_file : Parser[List[SExpression]] = rep(sexpression) ^^ debugrule

    // ------------ end of grammar --------------------

  }


}
