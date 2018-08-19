package gapt.formats.prover9

import scala.util.parsing.combinator.{ PackratParsers, RegexParsers }
import gapt.expr._

/** Prolog Style Term Parser */
object Prover9TermParser extends Prover9TermParserA {
  override def conssymb: Parser[String] = """([a-z][a-zA-Z0-9_]*)|([0-9]+)""".r
  override def varsymb: Parser[String] = """[A-Z][a-zA-Z0-9_]*""".r

}

/** LADR Style Term Parser */
object Prover9TermParserLadrStyle extends Prover9TermParserA {
  override def conssymb: Parser[String] = """([a-tA-Z][a-zA-Z0-9_]*)|([0-9]+)""".r
  override def varsymb: Parser[String] = """[u-z][a-zA-Z0-9_]*""".r

}

/**
 * Parser for first order formulas in the prover9 format.
 *
 * See [[http://www.cs.unm.edu/~mccune/mace4/manual/2009-11A/syntax.html]]
 * {{{
 * Right associative, infix operators: &, |, all, exists
 * Infix operators: =, !=, <, >, , <=, >=, ->, <-, <->
 * Operator precedence (higher up in the list means binds weaker i.e. operator is closer to the root):
 *    ->, <-, <->
 *    all, exists
 *    =, !=, <, >, , <=, >=
 *    -
 * Operators missing: +,*,@,/,\, /\, \/,'
 * Unhandled cases prover9 accepts (extended as exceptions are encountered):
 *    (all 1 P(1))
 * }}}
 */
trait Prover9TermParserA extends RegexParsers with PackratParsers {
  /* these two rules are abstract since the variable style decides the regexp for a variable */
  def conssymb: Parser[String]
  def varsymb: Parser[String]

  def parseFormula( s: String ): FOLFormula = parseAll( formula, s ) match {
    case Success( result, _ ) => result
    case NoSuccess( msg, input ) =>
      throw new Exception( "Error parsing prover9 formula '" + s + "' at position " + input.pos + ". Error message: " + msg )
  }

  def parseTerm( s: String ): FOLTerm = parseAll( term, s ) match {
    case Success( result, _ ) => result
    case NoSuccess( msg, input ) =>
      throw new Exception( "Error parsing prover9 term '" + s + "' at position " + input.pos + ". Error message: " + msg )
  }

  lazy val pformula: PackratParser[FOLFormula] = parens( formula ) | allformula | exformula
  lazy val formula: PackratParser[FOLFormula] = implication
  //precedence 800
  lazy val implication: PackratParser[FOLFormula] =
    ( dis_or_con ~ ( "<->" | "->" | "<-" ) ~ dis_or_con ) ^^ {
      case f ~ "->" ~ g  => Imp( f, g )
      case f ~ "<-" ~ g  => Imp( g, f )
      case f ~ "<->" ~ g => And( Imp( f, g ), Imp( g, f ) )
    } | dis_or_con

  lazy val dis_or_con: PackratParser[FOLFormula] = disjunction | conlit
  //precedence 790
  lazy val disjunction: PackratParser[FOLFormula] =
    ( conlit ~ ( "|" ~> disjunction ) ^^ { case f ~ g => Or( f, g ) } ) | conlit
  //precedence 780
  lazy val conlit: PackratParser[FOLFormula] = conjunction | qliteral
  lazy val conjunction: PackratParser[FOLFormula] =
    ( qliteral ~ ( "&" ~> conjunction ) ^^ { case f ~ g => And( f, g ) } ) | qliteral
  //precedence 750
  lazy val qliteral: PackratParser[FOLFormula] = allformula | exformula | literal2
  lazy val allformula: PackratParser[FOLFormula] = parens( allformula_ )
  lazy val exformula: PackratParser[FOLFormula] = parens( exformula_ )
  lazy val allformula_ : PackratParser[FOLFormula] =
    ( "all" ~> variable ~ ( allformula_ | exformula_ | literal2 ) ) ^^ { case v ~ f => All( v, f ) }
  lazy val exformula_ : PackratParser[FOLFormula] =
    ( "exists" ~> variable ~ ( allformula_ | exformula_ | literal2 ) ) ^^ { case v ~ f => Ex( v, f ) }

  //precedence 300
  lazy val literal2: PackratParser[FOLFormula] = pformula | atomWeq | negation
  lazy val negation: PackratParser[FOLFormula] = "-" ~> ( pformula | negation | atomWeq ) ^^ { x => Neg( x ) }

  def parens[T]( p: Parser[T] ): Parser[T] = "(" ~> p <~ ")"

  lazy val literal: PackratParser[FOLFormula] = iatom | negatom | posatom
  lazy val posatom: PackratParser[FOLFormula] = atom
  lazy val negatom: PackratParser[FOLFormula] = "-" ~> atom ^^ ( Neg( _ ) )
  lazy val atomWeq: PackratParser[FOLFormula] = iatom | atom
  lazy val atom: PackratParser[FOLFormula] = atom1 | atom2 | topbottom
  lazy val atom1: PackratParser[FOLFormula] = atomsymb ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
    case x ~ _ ~ params ~ _ => FOLAtom( x, params )
  }
  lazy val atom2: PackratParser[FOLFormula] = atomsymb ^^ ( FOLAtom( _, Nil ) )

  //infixatom
  lazy val iatom: PackratParser[FOLFormula] = term ~ """((<|>)=?)|(!?=)|[+\-*]""".r ~ term ^^ {
    case t1 ~ "=" ~ t2  => Eq( t1, t2 )
    case t1 ~ "!=" ~ t2 => Neg( Eq( t1, t2 ) )
    case t1 ~ sym ~ t2  => FOLAtom( sym, List( t1, t2 ) )
  }
  lazy val atomsymb: Parser[String] = """[a-zA-Z][a-zA-Z0-9_]*""".r
  lazy val term: PackratParser[FOLTerm] = ifunction | pfunction | noniterm
  lazy val ifunction: PackratParser[FOLTerm] =
    pfunction ~ """[+\-*/^v]""".r ~ pfunction ^^ {
      case t1 ~ sym ~ t2 => FOLFunction( sym, List( t1, t2 ) )
    }
  lazy val pfunction: PackratParser[FOLTerm] =
    ( noniterm | parens( ifunction ) ) ~ "'".? ^^ {
      case t1 ~ Some( _ ) => FOLFunction( "'", t1 )
      case t1 ~ None      => t1
    }
  lazy val noniterm: PackratParser[FOLTerm] = function | constant | variable
  lazy val function: PackratParser[FOLTerm] = conssymb ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
    case x ~ _ ~ params ~ _ => FOLFunction( x, params )
  }
  lazy val constant: PackratParser[FOLTerm] = conssymb ^^ ( FOLConst( _ ) )
  lazy val variable: PackratParser[FOLVar] = varsymb ^^ { FOLVar( _ ) }
  lazy val topbottom: PackratParser[FOLFormula] = "$" ~> ( "T" ^^ ( _ => Top() ) | "F" ^^ ( _ => Bottom() ) )

}

