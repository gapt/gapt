package at.logic.provers.prover9.lisp

import collection.{mutable, immutable}
import java.io.FileReader
import collection.immutable.PagedSeq
import util.parsing.input.{NoPosition, Position, Reader, PagedSeqReader}
import util.parsing.combinator.Parsers
import util.parsing.combinator.RegexParsers
import at.logic.provers.prover9.lisp

/**** Lisp SExpression Datatypes and Parser
 * This is a basic LISP S-expression parser, without quote character, macros or other fancy stuff.
 * Atoms have a reduced namespace and need to be extended if necessary.
 *
 * Some remarks:
 * (1) regexp parsers eat whitespace and newlines
 * (2) recursive cases have to be put first
 */


/* Basic Lisp Datastructures: Atom, Cons and List -- be careful with namespace collisions in scala.*.List.
 * Printing a Datastructure should output valid Lisp.
 */
sealed class SExpression

case class Atom(name : String) extends SExpression {
  override def toString = name
}

case class List(elements : immutable.List[SExpression] ) extends SExpression {
  def ::(head : SExpression) = lisp.List(head::elements)
  def ++(list2 : lisp.List) = lisp.List(elements ++ list2.elements)

  def lst2string[T](fun:(T=>String), seperator: String, l:immutable.List[T]) : String = l match {
    case immutable.Nil => ""
    case immutable.List(x) => fun(x)
    case x :: xs => fun(x)  + seperator + lst2string(fun, seperator, xs)
  }

  override def toString = "("+ lst2string(((x:Any) => x.toString), " ", elements) + ")"
  //def prepend(head : SExpression, list : lisp.List) = lisp.List(head::list.list)
}
case class Cons(car: SExpression, cdr : SExpression) extends SExpression {
  override def toString = "( " + car + " . " + cdr + ")"
}

class SExpressionParser extends SExpressionParser2
/* Parser for SExpressions  */
object SExpressionParser extends SExpressionParser {
  def dumpreader[T](r:Reader[T]) = {
    var reader = r
    println("=== dumping reader! ===")
    while (! reader.atEnd) {
      print(reader.first)
      reader = reader.rest
    }
    println()
  }

  def apply(fn : String) : immutable.List[SExpression] = {
//    val fis = new FileReader(fn)
//    val pagedseq = new PagedSeq(fis.read)
//    val reader = new PagedSeqReader(pagedseq)
//    parseAll(lisp_file, reader) match {
//      case Success(result, _) =>
//        fis.close()
        val r = new PagedSeqReader(new PagedSeq[Char](new FileReader(fn).read))
        val parser = new SExpressionParser
        parser.parse(r) match {
          case parser.Success(sexp, _) =>
            sexp
          case parser.NoSuccess(msg,_) =>
            dumpreader(r)
            throw new Exception("Ivy Parser Failed: "+msg)
        }
//        result
//      case NoSuccess(msg, r) =>
//        dumpreader(r)
//        throw new Exception("Ivy Parser Failed: "+msg)
//    }
  }
}


package tokens {
  sealed abstract class Token;
  case object LBRACK extends Token;
  case object RBRACK extends Token;
  case object DOT extends Token;
  case object NIL extends Token;
  case class STRING(s:String) extends Token;
  case class WORD(s:String) extends Token;
  case object COMMENT extends Token;
  case object EOF extends Token;
}


object ListReader {
  def apply(toks : immutable.List[tokens.Token]) : ListReader = ListReader(toks,toks)
  def apply(toks : immutable.List[tokens.Token], full : immutable.List[tokens.Token]) : ListReader =
    new ListReader(toks,full)
  /*
  {
    //caches results in a nested weak hash map -- full changes less, so it is the first index
    val outer = map.get(full)
    outer match {
      case None =>
        val m = new mutable.WeakHashMap[immutable.List[tokens.Token],ListReader]()
        val el =  new ListReader(toks,full)
        m(toks) = el
        el
      case Some(m) =>
        m.get(toks) match {
          case None =>
            val el =  new ListReader(toks,full)
            m(toks) = el
            el
          case Some(el) =>
            el
        }
    }
  } */

  val map = mutable.WeakHashMap[immutable.List[tokens.Token],
    mutable.WeakHashMap[immutable.List[tokens.Token],ListReader]]()
}
class ListReader(val list : immutable.List[tokens.Token], val full : immutable.List[tokens.Token])
  extends Reader[tokens.Token] {
  //lazy val rest-full = (rest, full) //used as index in the hashtable
  def atEnd = list.isEmpty
  def first : tokens.Token = { if (atEnd) tokens.EOF else list.head}
  def rest : ListReader = if (atEnd) this else ListReader(list.tail, full)
  def pos : Position =
    if (list.isEmpty) NoPosition else IntPosition(full.size-list.size)

}

object IntPosition {
  def apply(i:Int) = new IntPosition(i)
  /*
  {
    //caches positions in a weak hashmap (i.e. may be garbage collected)
    val r = map.get(i)
    r match {
      case None =>
        val p = new IntPosition(i)
        map(i) = p
        p
      case Some(p) =>
        p
    }
  } */
  val map = mutable.WeakHashMap[Int, IntPosition]()
}
class IntPosition(val i:Int) extends Position {
  def line = i;
  def column = 0
  def lineContents = "(no information)"
}

class Tokenizer extends RegexParsers {
  import at.logic.provers.prover9.lisp.tokens._

  def debug(s:String) = {println("DEBUG: "+s)}
  def debugrule[T](t:T) : T = { debug("dr: "+t.toString) ; t}

  def token : Parser[Token] = """"[^"]*"""".r ^^ STRING |
                              """[nN][iI][lL]""".r ^^ (x => NIL) |
                              """[a-zA-Z0-9=_+\-*/]+""".r ^^ WORD |
                              "." ^^ (x => DOT) |
                              "(" ^^ (x => LBRACK) |
                              ")" ^^ (x => RBRACK) |
                              """;;.*""".r ^^ (x => COMMENT)

  def tokens : Parser[immutable.List[Token]] = rep(token)
}

class SExpressionParser2 extends Parsers {
  import tokens._
  type Elem = Token

  val tokenizer = new Tokenizer()

  def debug(s:String) = {}
  def wrap[T](s:T) = { debug("wrapping: '"+s+"'"); immutable.List(s) }
  def prepend[T](l : ~[T, immutable.List[T]]) : immutable.List[T] = { debug("prepending: '"+l+"'"); l match { case ~(l1,l2) => l1 :: l2  } }
  def prepend_tolisplist(l : ~[SExpression, SExpression]) : lisp.List = {
      l match { case ~(l1,lisp.List(l2)) => lisp.List(l1 :: l2)
        case _ => throw new Exception("Somethings wrong in the parser implementation!")
      }
    }

  def LB : Parser[String] = accept("(", {case LBRACK => "("} )
  def RB : Parser[String] = accept("(", {case RBRACK => ")"} )
  def D : Parser[String] = accept(".", {case DOT => "."} )
  def N : Parser[String] = accept("nil", {case NIL => "nil"} )

  def atom :Parser[lisp.Atom] = accept("word", {case WORD(n) => lisp.Atom(n)}) |
                                  accept("string", {case STRING(n) => lisp.Atom(n)})

  def nil : Parser[lisp.List] =  (LB ~ RB) ^^ (x => lisp.List(Nil)) |
                                 (N) ^^ (x => lisp.List(Nil))

  def list : Parser[lisp.List] = LB ~> (rep(sexp) ^^ lisp.List) <~ RB | nil
  def list_ : Parser[lisp.List] = ((sexp ^^ ((x:SExpression) => lisp.List( x :: Nil))) <~ RB) |
                                   (((sexp ~ list_) ^^ prepend_tolisplist) <~ RB)

  def dot : Parser[SExpression] =  (LBRACK ~> sexp ~ D ~ sexp <~ RBRACK) ^^ (
    (exp: ~[~[SExpression, String], SExpression]) => {
      val car ~ _ ~ cdr = exp
      cdr match {
        case lisp.List(elems) => lisp.List(car::elems)
        case _ => lisp.Cons(car,cdr)
      }

    })

  def sexp : Parser[SExpression] = list | dot | atom
  def lisp_file : Parser[immutable.List[SExpression]] = rep(sexp) <~ EOF


  def parse(in : CharSequence) = {
    tokenizer.parseAll(tokenizer.tokens, in) match {
      case tokenizer.Success(result,_) =>
        val r = result filter (_ match { case COMMENT => false; case _ => true} )
        //println(r)
        phrase(lisp_file)(ListReader(r))
    }
  }
  def parse(in : Reader[Char]) = {
    tokenizer.parseAll(tokenizer.tokens, in) match {
      case tokenizer.Success(result,_) =>
        val r = result filter (_ match { case COMMENT => false; case _ => true} )
        //println(r)
        phrase(lisp_file)(ListReader(r))
    }
  }
}

/* The actual Parser, lexing and parsing is mixed which makes the grammar look a bit ugly sometimes */
class SExpressionParser1 extends RegexParsers {
  //override val whiteSpace = """($|\s+|(\s*;;.*)*)""".r

  def debug(s:String) = ()
  // --- parser transformers for putting elements into lists, concatenating parsing results, etc
  def wrap[T](s:T) = { debug("wrapping: '"+s+"'"); immutable.List(s) }
  def prepend[T](l : ~[T, immutable.List[T]]) : immutable.List[T] = { debug("prepending: '"+l+"'"); l match { case ~(l1,l2) => l1 :: l2  } }
  def prepend2[T](l : ~[~[T,T],immutable.List[T]]) : immutable.List[T] = { debug("prepending: '"+l+"'"); l match { case l1 ~ l2 ~ l3 => l1 :: l2 :: l3 } }
  def concat[T](l : ~[immutable.List[T],immutable.List[T]]) : immutable.List[T] = { debug("concatenating: '"+l+"'"); l match { case ~(l1,l2) => l1 ++ l2  } }

  def prepend_tolisplist(l : ~[SExpression, SExpression]) : lisp.List = {
    l match { case ~(l1,lisp.List(l2)) => lisp.List(l1 :: l2)
    case _ => throw new Exception("Somethings wrong in the parser implementation!")
    }
  }
  def concat_lisplists(l : ~[SExpression,SExpression]) : lisp.List = {
    l match { case ~(lisp.List(l1),lisp.List(l2)) => lisp.List(l1 ++ l2)
    case _ => throw new Exception("Somethings wrong in the parser implementation!")
    }
  }

  def debugrule[T](t:T) : T = { debug("dr: "+t.toString) ; t}

  def wrap_inlisplist(s:SExpression) = {  lisp.List(s::Nil) }

  // ------------ start of grammar --------------------

  //def eof : Parser[String] = """\z""".r
  //def non_delimiter : Parser[String] = """[^,\(\)\[\]]([^,\.\(\)\[\]+])?""".r
  def comment : Parser[String] = """;;.*""".r
  def comments : Parser[String] = comment ~ comments ^^ ((x : ~[String,String]) => {val ~(s1,s2) = x; s1 + s2}) | comment

  //def comments : Parser[String] = """""".r

  //    def word : Parser[IvyToken] = """[^,\(\)\[\]\s]([^,\.\(\)\[\]\s]+)?""".r ^^ IvyToken
  //def word : Parser[IvyToken] = """[^,\.\(\)\[\]\s]*[^,\(\)\[\]\s][^,\.\(\)\[\]\s]*""".r ^^ IvyToken.apply
  //TODO: extend definition of word
  def word : Parser[SExpression] = """[a-zA-Z0-9=_+\-*/]+""".r ^^ lisp.Atom   //contains only very restricted strings
  def string :Parser[SExpression] = """"[^"]*"""".r ^^ lisp.Atom              //arbitrary strings wrapped in " "

  def atom : Parser[SExpression] = string | word

  def nil : Parser[SExpression] = (("(") ~> (")") | """[nN][iI][lL]""".r) ^^ ((x:Any) => lisp.List(Nil)) //empty list

  def list : Parser[SExpression] = (nil | ("(") ~> list_ <~ (")"))            // arbitrary list
  def list_ : Parser[SExpression] =  ( (sexpression ^^ wrap_inlisplist) ~ list_ ) ^^ concat_lisplists |
      ( (sexpression ^^ wrap_inlisplist))

  // cons: cons'es are converted to lists if possible (second argument is a list)
  def cons : Parser[SExpression] = (("(") ~> sexpression) ~ (".") ~ (sexpression <~ (")")) ^^ (
    (exp: ~[~[SExpression, String], SExpression]) => {
      val car ~ _ ~ cdr = exp
      cdr match {
        case lisp.List(elems) => lisp.List(car::elems)
        case _ => lisp.Cons(car,cdr)
      }

    })

  def newline : Parser[String] = "$".r ~> newline | "$".r
  //parsing of comments is a bit expensive :(
  def sexpression_ : Parser[SExpression] =  ( list | atom | cons)
  def sexpression : Parser[SExpression] =  opt(comments) ~> sexpression_  <~ opt(comments)

  //a file is a list of sexpressions
  def lisp_file : Parser[immutable.List[SExpression]] = rep(sexpression)  <~ opt(comments) ^^ debugrule

  def parse(in:CharSequence) = parseAll(lisp_file, in)
  def parse(in:Reader[Char]) = parseAll(lisp_file, in)
  // ------------ end of grammar --------------------

}
