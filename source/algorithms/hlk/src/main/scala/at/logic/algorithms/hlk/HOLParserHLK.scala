package at.logic.algorithms.hlk.parser

import at.logic.algorithms.hlk.HLKFormulaParser
import at.logic.language.hol.{HOLVar, HOLFormula, HOLExpression}
import util.parsing.combinator.RegexParsers
import collection.immutable
import at.logic.language.fol.FOLExpression
import at.logic.language.lambda.types.{Ti, To, TA}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import util.parsing.input.Reader
import util.parsing.combinator.token.Tokens
import util.parsing.combinator.lexical.{Lexical, Scanners}
import util.parsing.combinator.syntactical.{StdTokenParsers, StandardTokenParsers}

/**
 * parser for hol formulas in the hlk format
 */
abstract class HOLParser(symbol_map : HOLParser.SymbolMap) extends HLKFormulaParser with StdTokenParsers {

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

  def simpletype : Parser[TA] = TYPE("i") ^^ { x => Ti() } | TYPE("o") ^^ { x => To() }
  def complextype : Parser[TA] =   simpletype |
    (simpletype ~ (ARROW ~> simpletype)  |
     simpletype ~ (ARROW ~> LPARENS ~> complextype <~ RPARENS)  |
     (LPARENS ~> complextype <~ RPARENS) ~ (ARROW ~> simpletype) |
     (LPARENS ~> complextype <~ RPARENS) ~ (ARROW ~> LPARENS ~> complextype <~ RPARENS)) ^^ { case t1 ~ t2 => t1 -> t2 }
  */
}

object HOLParser {
  type SymbolMap = immutable.HashMap[String, HOLExpression]
  val emptySymbolMap = immutable.HashMap.empty[String, HOLExpression]

//  def apply(symbolMap : SymbolMap) = new HOLParser(symbolMap)

}

trait HLKTokens extends Tokens {
  abstract sealed class Tokens
  case object LPARENS extends Tokens
  case object RPARENS extends Tokens
  case object LBRACK extends Tokens
  case object RBRACK extends Tokens
  case object COLON extends Tokens
  case object COMMA extends Tokens
  case object COMMENT extends Tokens
  case object NEG extends Tokens
  case object AND extends Tokens
  case object OR extends Tokens
  case object IMPL extends Tokens
  case object ALL extends Tokens
  case object EXISTS extends Tokens
  case object LAMBDA extends Tokens
  case object ARROW extends Tokens
  case class TYPE(name : String) extends Tokens
  case class NAME(text : String) extends Tokens

/*
  class Tokenizer extends Lexical {
    override type Token = HLKTokens

    val name_re = """[a-zA-Z0-9]+""".r

    lazy val token : Parser[Tokens] =
      (letter ^^ (_ match {
        case name_re => NAME("")
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
        case "i" => TYPE("i")
        case "o" => TYPE("o")
      })) |
        ((letter ~ letter) ^^ {_ match {case "-"~">" => IMPL } })



    override def whitespace : Parser[Any] = rep(whitespaceChar)
 */
/*
    lazy val tokens : Parser[List[Tokens]] = token.+

    lazy val token : Parser[Tokens] =
      ("(" ^^ (x => LPARENS)) |
      (")" ^^ (x => RPARENS)) |
      ("[" ^^ (x => LBRACK)) |
      ("]" ^^ (x => RBRACK)) |
      (":" ^^ (x => COLON)) |
      ("," ^^ (x => COMMA)) |
      ("-" ^^ (x => NEG)) |
      ("&" ^^ (x => AND)) |
      ("|" ^^ (x => OR)) |
      ("!" ^^ (x => ALL)) |
      ("?" ^^ (x => EXISTS)) |
      ("->" ^^ (x => IMPL)) |
      ("\\" ^^ (x => LAMBDA)) |
      (">" ^^ (x => ARROW)) |
      ("""[a-zA-Z0-9]+""".r ^^ NAME) |
      ("""[io]""".r ^^ TYPE)

  }
   */
}