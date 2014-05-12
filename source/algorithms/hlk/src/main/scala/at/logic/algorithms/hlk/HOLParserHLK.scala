package at.logic.algorithms.hlk.parser

import at.logic.algorithms.hlk.HLKFormulaParser
import at.logic.language.hol.{HOLVar, HOLFormula, HOLExpression}
import util.parsing.combinator.RegexParsers
import at.logic.language.fol.FOLExpression
import at.logic.language.lambda.types.{Ti, To, TA}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import util.parsing.input.Reader
import util.parsing.combinator.token.Tokens
import util.parsing.combinator.lexical.{Lexical, Scanners}
import util.parsing.combinator.syntactical.{TokenParsers, StdTokenParsers, StandardTokenParsers}
import scala.collection.immutable.HashMap

/**
 * parser for hol formulas in the hlk format
 */
abstract class HOLParser(symbol_map : HOLParser.SymbolMap) extends HLKFormulaParser with TokenParsers {
  //type Tokens <: HLKTokens
  //val lexical =
  import lexical._


  /*
  def term: Parser[HOLExpression] = LPARENS ^^ { case NAME(name) => symbol_map(name) }
  def formula: Parser[HOLFormula] = LPARENS ^^ { case NAME(name) => symbol_map(name).asInstanceOf[HOLFormula] }
  def variable: Parser[HOLVar] = LPARENS ^^ { case NAME(name) => symbol_map(name).asInstanceOf[HOLVar] }

  def atom : Parser[HOLExpression] = acceptMatch("some name",{ case n@NAME(_) => n}) ~ (COLON ~> complextype).? ^^
    { _ match {
        case NAME(name) ~ None => symbol_map(name).asInstanceOf[HOLVar]
        case NAME(name) ~ Some(exptype) => HOLVar(VariableStringSymbol(name), exptype)
        case _ => throw new Exception("Error in hlk hol parser!")
      }
    }
  */

  //def bla : Parser[Elem] = accept(LPARENS)


  //def simpletype : Parser[TA] = TYPE("i") ^^ { x => Ti() } | TYPE("o") ^^ { x => To() }


  /*
  def complextype : Parser[TA] =   simpletype |
    (simpletype ~ (ARROW ~> simpletype)  |
     simpletype ~ (ARROW ~> LPARENS ~> complextype <~ RPARENS)  |
     (LPARENS ~> complextype <~ RPARENS) ~ (ARROW ~> simpletype) |
     (LPARENS ~> complextype <~ RPARENS) ~ (ARROW ~> LPARENS ~> complextype <~ RPARENS)) ^^ { case t1 ~ t2 => t1 -> t2 }


    */
}

object HOLParser {
  type SymbolMap = HashMap[String, HOLExpression]
  val emptySymbolMap = HashMap.empty[String, HOLExpression]

//  def apply(symbolMap : SymbolMap) = new HOLParser(symbolMap)

}

trait HLKTokens  {
  abstract trait HToken  {
    def chars : String
    def unapply(s:String) = if (chars == s) Some(chars) else None
  }

  object LPARENS extends HToken { def chars = "(" }
  object RPARENS extends HToken { def chars = ")" }
  object LBRACK extends HToken { def chars = "[" }
  object RBRACK extends HToken { def chars = "]" }
  object COLON extends HToken { def chars = ":" }
  object COMMA extends HToken { def chars = "," }
  object NEG extends HToken { def chars = "-" }
  object AND extends HToken { def chars = "&" }
  object OR extends HToken { def chars = "|" }
  object IMPL extends HToken { def chars = "->" }
  object ALL extends HToken { def chars = "!" }
  object EXISTS extends HToken { def chars = "?" }
  object LAMBDA extends HToken { def chars = "\\" }
  object ARROW extends HToken { def chars = ">" }
  case class NAME(chars : String) extends HToken
  case object ERROR extends HToken { def chars ="ERROR"}

  class Tokenizer extends Lexical {
    override type Token = HToken

    val char_re = """[a-zA-Z0-9\(\)\[\]:,\-&\|\\!\?<>]""".r
    val name_re = """[a-zA-Z0-9]+""".r

    def word : Parser[String] = (elem("letter, number or operator", _.toString match {
      case char_re() => true;
      case _ => false }
    )+) ^^ (_.mkString(""))

    override def token : Parser[Token] =
      (word  ^^ (_ match {
        case name_re() => NAME("")
        case "(" => LPARENS
        case ")" => RPARENS
        case "[" => LBRACK
        case "]" => RBRACK
        case ":" => COLON
        case "," => COMMA
        case "-" => NEG
        case "&" => AND
        case "|" => OR
        case "!" => ALL
        case "?" => EXISTS
        case "\\" => LAMBDA
        case ">" => ARROW
        case "->" => IMPL
        //case _ => errorToken("")
      }))

    override def whitespace : Parser[Any] = rep(whitespaceChar)
 }
}
