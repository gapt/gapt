package at.logic.parsing.lisp

import java.io.FileReader
import util.parsing.input.{NoPosition, Position, Reader, PagedSeqReader}
import util.parsing.combinator.Parsers
import util.parsing.combinator.RegexParsers
import at.logic.parsing.lisp
import util.parsing.combinator.PackratParsers
import scala.collection.immutable.PagedSeq
import scala.collection.mutable
import scala.collection.immutable
import at.logic.utils.dssupport.ListSupport.lst2string

/**** Lisp SExpression Datatypes and Parser
 * This is a basic LISP S-expression parser, without quote character, macros or other fancy stuff.
 * Atoms have a reduced namespace and need to be extended if necessary.
 *
 * Some remarks:
 * (1) regexp parsers eat whitespace and newlines
 * (2) recursive cases have to be put first
 */


/* Basic Lisp Datastructures: Atom, Cons and List 
 * Namespace collisions in scala.*.List
 * Printing a Datastructure should output valid Lisp.
 */
sealed class SExpression

case class Atom(name : String) extends SExpression {
  override def toString = name
}

case class List(elements : immutable.List[SExpression] ) extends SExpression {
  def ::(head : SExpression) = lisp.List(head::elements)
  def ++(list2 : lisp.List) = lisp.List(elements ++ list2.elements)

  override def toString = "("+ lst2string(((x: SExpression) => x.toString), " ", elements) + ")"
  //def prepend(head : SExpression, list : lisp.List) = lisp.List(head::list.list)
}

case class Cons(car: SExpression, cdr : SExpression) extends SExpression {
  override def toString = "( " + car + " . " + cdr + ")"
}

/* Parser for SExpressions  */
object SExpressionParser extends SExpressionParser {
  def dumpreader[T](r:Reader[T]) : String = dumpreader_(r).mkString(" ")
  private def dumpreader_[T](r:Reader[T]) : immutable.List[T] = {
    var reader = r
    if (reader.atEnd) Nil
    else reader.first :: dumpreader_(reader.rest)
  }

  def apply(fn : String) : immutable.List[SExpression] = parseFile(fn)

  def parseFile(fn:String) : immutable.List[SExpression] = {
        val r = new PagedSeqReader(new PagedSeq[Char](new FileReader(fn).read))
        val parser = new SExpressionParser
        parser.parse(r) match {
          case parser.Success(sexp, _) =>
            sexp
          case parser.NoSuccess(msg, in) =>
            println(dumpreader(in.rest))
            throw new Exception("S-Expression Parser Failed: "+msg + " at "+in.pos+" with remaning input:"+dumpreader(in.rest))
        }
  }

  def parseString(s:String) : immutable.List[SExpression] = {
    val parser = new SExpressionParser
    parser.parse(s) match {
      case parser.Success(sexp, _) =>
        sexp
      case parser.NoSuccess(msg,in) =>
        throw new Exception("S-Expression Parser Failed: "+msg + " at "+in.pos+" with remaning input: "+dumpreader(in.rest))
    }

  }


}


package tokens {
  sealed abstract class Token;
  case object LBRACK extends Token { override def toString = "(" };
  case object RBRACK extends Token { override def toString = ")" };;
  case object DOT extends Token { override def toString = "." };
  case object NIL extends Token { override def toString = "nil" };
  case class STRING(s:String) extends Token { override def toString = "\""+s+"\"" };
  case class WORD(s:String) extends Token { override def toString = s };
  case object COMMENT extends Token { override def toString = "" };
  case object EMPTYFILE extends Token { override def toString = "" };
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
        val m = new WeakHashMap[List[tokens.Token],ListReader]()
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
  lazy val position = IntPosition(full.size-list.size)
  def atEnd = list.isEmpty
  def first : tokens.Token = { if (atEnd) tokens.EMPTYFILE else list.head }
  def rest : ListReader = {
    if (atEnd)
      throw new Exception("Tried to get rest of a list reader already at its end!")
    else
      ListReader(list.tail, full)
  }

  def pos : Position =
    if (list.isEmpty) NoPosition else position

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
  //val map = mutable.WeakHashMap[Int, IntPosition]()
}
class IntPosition(val i:Int) extends Position {
  def line = 0
  def column = i
  def lineContents = "(no information)"
}

class Tokenizer extends RegexParsers {
  import at.logic.parsing.lisp.tokens._

  //def debug(s:String) = {println("DEBUG: "+s)}
  //def debugrule[T](t:T) : T = { debug("dr: "+t.toString) ; t}

  lazy val token : Parser[Token] = """"[^"]*"""".r ^^ STRING |
                              """[nN][iI][lL]""".r ^^ (x => NIL) |
                              """[a-zA-Z0-9=_+\-*/<>:.]*[a-zA-Z0-9=_+\-*/<>:]+[a-zA-Z0-9=_+\-*/<>:.]*""".r ^^ WORD |
                              "." ^^ (x => DOT) |
                              "(" ^^ (x => LBRACK) |
                              ")" ^^ (x => RBRACK) |
                              """;;.*""".r ^^ (x => COMMENT)

  lazy val tokens : Parser[immutable.List[Token]] = rep(token)
}

class SExpressionParser extends Parsers {
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

  lazy val LB : Parser[String] = accept("(", {case LBRACK => "("} )
  lazy val RB : Parser[String] = accept(")", {case RBRACK => ")"} )
  lazy val D : Parser[String] = accept(".", {case DOT => "."} )
  lazy val N : Parser[String] = accept("nil", {case NIL => "nil"} )

  lazy val atom :Parser[SExpression] = nil |
                                  accept("word", {case WORD(n) => lisp.Atom(n)}) |
                                  accept("string", {case STRING(n) => lisp.Atom(n)})

  lazy val nil : Parser[lisp.List] =  (LB ~! RB) ^^ (x => lisp.List(Nil)) |
                                 (N) ^^ (x => lisp.List(Nil))



  lazy val lcprefix : Parser[SExpression] = LB ~> (sexp ~ list_or_cons) ^^
    { case x ~ ((is_cons, lisp.List(xs))) => if (is_cons) {
      xs match {
        case lisp.List(elems)::Nil => lisp.List(x::elems)
        case cdr::Nil => lisp.Cons(x,cdr)
        case Nil => throw new Exception("Error during cons parsing - subrule didn't pass cdr!")
      }
    } else {
      lisp.List(x::xs)
    } }

  lazy val list_or_cons : Parser[(Boolean,lisp.List)] =
      DOT ~> sexp <~ RB ^^ { (l : SExpression) => (true,  lisp.List(l::Nil)) }|
      rep(sexp) <~ RB ^^   { (l : immutable.List[SExpression]) => (false, lisp.List(l)) }


  //lazy val list : Parser[lisp.List] = LB ~> (rep1(sexp) ^^ lisp.List) <~ RB |  nil
/*
  lazy val dot : Parser[SExpression] =  (LBRACK ~> sexp ~! D ~! sexp <~ RBRACK) ^^ (
    (exp: ~[~[SExpression, String], SExpression]) => {
      val car ~ _ ~ cdr = exp
      cdr match {
        case lisp.List(elems) => lisp.List(car::elems)
        case _ => LispCons(car,cdr)
      }

    })
  */
  lazy val sexp : Parser[SExpression] = lcprefix | atom
  lazy val lisp_file : Parser[immutable.List[SExpression]] = rep(sexp) | (EMPTYFILE ^^ { _ => Nil} )

  def parse(in : CharSequence) = {
    tokenizer.parseAll(tokenizer.tokens, in) match {
      case tokenizer.Success(result,_) =>
        val r = result filter (_ match { case COMMENT => false; case _ => true} )
        //val s : Scanners
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

