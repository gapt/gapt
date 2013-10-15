package at.logic.algorithms.hlk

import scala.util.parsing.combinator.{PackratParsers, RegexParsers}
import at.logic.parsing.language.hlk.{ast, DeclarationParser, HLKHOLParser}
import at.logic.parsing.language.hlk.ast.LambdaAST
import scala.util.parsing.input.PagedSeqReader
import scala.collection.immutable.PagedSeq
import java.io.FileReader
import at.logic.language.lambda.types.TA

abstract class Token
case class RToken(rule:String, name : String, antecedent: List[LambdaAST], succedent:List[LambdaAST]) extends Token
case class TToken(decltype : String, names : List[String], types : TA ) extends Token

abstract class LToken;
case class ALLL(antecedent : List[String], succedent : List[String]) extends LToken;
case class ALLR(antecedent : List[String], succedent : List[String]) extends LToken;
case class EXL(antecedent : List[String], succedent : List[String]) extends LToken;
case class EXR(antecedent : List[String], succedent : List[String]) extends LToken;
case class ANDL(antecedent : List[String], succedent : List[String]) extends LToken;
case class ANDR(antecedent : List[String], succedent : List[String]) extends LToken;
case class ORL(antecedent : List[String], succedent : List[String]) extends LToken;
case class ORR(antecedent : List[String], succedent : List[String]) extends LToken;
case class IMPL(antecedent : List[String], succedent : List[String]) extends LToken;
case class IMPR(antecedent : List[String], succedent : List[String]) extends LToken;
case class NEGL(antecedent : List[String], succedent : List[String]) extends LToken;
case class NEGR(antecedent : List[String], succedent : List[String]) extends LToken;
case class EQL(antecedent : List[String], succedent : List[String]) extends LToken;
case class EQR(antecedent : List[String], succedent : List[String]) extends LToken;
case class WEAKL(antecedent : List[String], succedent : List[String]) extends LToken;
case class WEAKR(antecedent : List[String], succedent : List[String]) extends LToken;
case class CONTRL(antecedent : List[String], succedent : List[String]) extends LToken;
case class CONTRR(antecedent : List[String], succedent : List[String]) extends LToken;
case class CUT(antecedent : List[String], succedent : List[String]) extends LToken;
case class DEF(antecedent : List[String], succedent : List[String]) extends LToken;
case class BETA(antecedent : List[String], succedent : List[String]) extends LToken;
case class INSTLEMMA(name: String, antecedent : List[String], succedent : List[String]) extends LToken;
case class INSTAXIOM(name: String, antecedent : List[String], succedent : List[String]) extends LToken;
case class EQAXIOM(name: String, antecedent : List[String], succedent : List[String]) extends LToken;
case class CONTINUEWITH(name: String) extends LToken;
case class CONTINUEFROM(name: String, antecedent: List[String], succedent: List[String]) extends LToken;

trait LatexReplacementParser extends DeclarationParser {
  override lazy val abs : PackratParser[LambdaAST] =
      ("\\lambda" ~ atom2 ~ formula) ^^ { case _ ~ v ~ f => ast.Abs(v, f) }



  override lazy val appOrAtomWeq : PackratParser[LambdaAST] =
    (parens("@" ~> rep1(formula)) |
      ("\\apply" ~> "{" ~> rep1(formula) <~ "}"))  ^^ { x => x match {
      case List(elem) => elem
      case list => ast.App(list)
    }
    } | atomWeq

  lazy val latexmacros : PackratParser[LambdaAST] =
    ("\\ite{" ~> formula <~ "}") ~ ("{" ~> formula <~ "}") ~ ("{" ~> formula <~ "}") ^^ {
      case f1 ~ f2 ~ f3 => ast.App(List(ast.Var("ite"),f1,f2,f3))
    } |
    ("\\benc{" ~> formula <~ "}") ^^ {
      case f1  => ast.App(List(ast.Var("be"),f1))
    }|
    ("\\ienc{" ~> formula <~ "}") ^^ {
      case f1  => ast.App(List(ast.Var("ie"),f1))
    }

  override lazy val atom : PackratParser[LambdaAST] =
    latexmacros | atom1 | atom2 | topbottom

  override lazy val iatom2 : PackratParser[LambdaAST] = iatom3 ~ """([+\-]|\\bm)""".r  ~ iatom3 ^^ { _ match {
      case t1 ~ "\\bm" ~ t2  => ast.App(List(ast.Var("bm"), t1, t2) ) //TODO: change to \dotdiv and modify prooftool etc
      case t1 ~ sym ~ t2  => ast.App(List(ast.Var(sym), t1, t2) )
    }
  } | iatom3

}

object HybridLatexParser extends HybridLatexParser
class HybridLatexParser extends DeclarationParser with LatexReplacementParser {

  def parseFile(fn : String) : List[Token] = {
    val reader = new PagedSeqReader(new PagedSeq[Char](new FileReader(fn).read))

    parseAll( rules, reader) match {
      case Success(r, _) => r
      case NoSuccess(msg, input) =>
        throw new Exception("Error parsing Hybrid Latex/LK in "+fn+" at position "+input.pos +": "+msg)
    }
  }

  def parse(in : CharSequence) : List[Token] = {
    parseAll( rules, in) match {
      case Success(r, _) => r
      case NoSuccess(msg, input) =>
        throw new Exception("Error parsing Hybrid Latex/LK at position "+input.pos +": "+msg)
    }
  }

  override def d[T](r:T) :T = { println(r);  r}

  lazy val rules : PackratParser[List[Token]] = rep1((rule1|rule2|rule3|decl|comment) )

  lazy val comment : PackratParser[RToken] =  ("%" ~> "[^%]*".r <~ "%") ^^ { RToken("COMMENT", _, Nil, Nil) }

  lazy val rule1 : PackratParser[RToken] = (("\\" ~> "CONTINUEWITH" <~ "{" ) ~ atom  <~ "}" ) ^^ {
    _ match {
      case cw ~ atom  => RToken(cw, "", Nil, List(atom))
    }
  }

  lazy val rule2 : PackratParser[RToken] = ("\\" ~>
    "(AX|ALL[LR]|EX[LR]|AND[LR]|OR[LR]|IMP[LR]|NEG[LR]|EQ[LR]|WEAK[LR]|CONTR[LR]|CUT|DEF|BETA)".r
      <~ "{") ~ (repsep(formula, ",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}") ^^ {
    case name ~ antecedent ~ succedent => RToken(name, "", antecedent, succedent)
  }


  lazy val rule3 : PackratParser[RToken] = ("\\" ~> "(INSTLEMMA|INSTAXIOM|CONTINUEFROM|EQAXIOM)".r
    <~ "{" <~ "([^}]+:)?".r ) ~ (repsep(formula, ",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}")  ^^ {
    case name ~ arg1 ~ antecedent ~ succedent => RToken(name, arg1.toString, antecedent, succedent)
  }

  lazy val decl : PackratParser[TToken] = ("\\" ~> "(CONSTDEC|VARDEC)".r <~ "{") ~
    (rep1sep(symbolnames, ",") <~ "}") ~ ("{" ~> complexType <~ "}") ^^ { _ match {
    case "CONSTDEC" ~ namest ~ (types:TA) => TToken("CONST", namest, types)
    case "VARDEC" ~ namest ~ (types:TA) => TToken("VAR", namest, types)
  }
  }


  def splitAtOutermostComma(s:String) : List[String] = splitAtOutermostComma(s, "", List(), 0).reverse
  def splitAtOutermostComma(s:String, current : String, acc : List[String], level : Int) : List[String] = {
    if (s.isEmpty) {
      require(level == 0, "Problem splitting a list of formulas apart: there are still "+level+" parenthesis left open!")
      if (current.isEmpty) acc else current::acc
    } else {
      s.head match {
        case '(' =>
          splitAtOutermostComma(s.tail, current+s.head, acc, level + 1 )
        case ')' =>
          require(level > 0, "Problem splitting a list of formulas apart: trying to close parenthesis without corresponding open one! "+s)
          splitAtOutermostComma(s.tail, current+s.head, acc, level - 1 )
        case ',' if (level == 0) =>
          splitAtOutermostComma(s.tail, "", current::acc, level)
        case _ =>
          splitAtOutermostComma(s.tail, current+s.head, acc, level )
      }
    }

  }




}
