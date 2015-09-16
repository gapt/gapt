package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._

import scala.util.parsing.combinator._

class TPTPParser extends RegexParsers with PackratParsers {
  lazy val formula: PackratParser[FOLFormula] = dbl_impl

  lazy val dbl_impl: PackratParser[FOLFormula] = (
    impl ~ "<=>" ~ dbl_impl ^^ {
      case f1 ~ _ ~ f2 =>
        And( Imp( f1, f2 ), Imp( f2, f1 ) )
    }
    | impl ~ "<~>" ~ impl ^^ {
      case f1 ~ _ ~ f2 =>
        And( Or( f1, f2 ), Or( Neg( f2 ), Neg( f1 ) ) )
    }
    | impl
  )

  lazy val impl: PackratParser[FOLFormula] = (
    and ~ "=>" ~ impl ^^ { case f1 ~ _ ~ f2 => Imp( f1, f2 ) }
    | and
  )

  lazy val and: PackratParser[FOLFormula] = (
    or ~ "&" ~ and ^^ { case f1 ~ _ ~ f2 => And( f1, f2 ) }
    | or
  )

  lazy val or: PackratParser[FOLFormula] = (
    neg ~ "|" ~ or ^^ { case f1 ~ _ ~ f2 => Or( f1, f2 ) }
    | neg
  )

  lazy val neg: PackratParser[FOLFormula] = (
    ( "-" | "~" ) ~> neg ^^ { case f => Neg( f ) }
    | quantified
  )

  lazy val quantified: PackratParser[FOLFormula] = (
    "!" ~ "[" ~> repsep( variable, "," ) ~ "]" ~ ":" ~ quantified ^^ {
      case vars ~ _ ~ _ ~ form =>
        vars.foldLeft( form )( ( f, v ) => All( v, f ) )
    }
    | "?" ~ "[" ~> repsep( variable, "," ) ~ "]" ~ ":" ~ quantified ^^ {
      case vars ~ _ ~ _ ~ form =>
        vars.foldLeft( form )( ( f, v ) => Ex( v, f ) )
    }
    | neg | atom
  )

  lazy val atom: PackratParser[FOLFormula] = falseTrue | equal | not_eq | eq | real_atom | quantified | "(" ~> formula <~ ")"
  lazy val falseTrue = "$" ~> ( "false" ^^ { _ => Bottom() } | "true" ^^ { _ => Top() } )
  lazy val real_atom: PackratParser[FOLFormula] = name ~ opt( "(" ~> repsep( term, "," ) <~ ")" ) ^^ {
    case pred ~ Some( args ) => FOLAtom( pred, args )
    case pred ~ None         => FOLAtom( pred )
  }
  lazy val equal = ( "$equal(" | "equal(" ) ~> term ~ "," ~ term <~ ")" ^^ { case ( t ~ _ ~ s ) => Eq( t, s ) }
  lazy val eq: PackratParser[FOLFormula] = term ~ "=" ~ term ^^ {
    case t1 ~ _ ~ t2 => Eq( t1, t2 )
  }
  lazy val not_eq: PackratParser[FOLFormula] = term ~ "!=" ~ term ^^ {
    case t1 ~ _ ~ t2 => Neg( Eq( t1, t2 ) )
  }

  def term: Parser[FOLTerm] = variable | function | constant
  def function: Parser[FOLTerm] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ { case f ~ _ ~ args => FOLFunction( f, args ) }
  def constant: Parser[FOLConst] = name ^^ { case n => FOLConst( n ) }
  def variable: Parser[FOLVar] = """[_A-Z0-9][_A-Z0-9$a-z]*""".r ^^ { case n => FOLVar( n ) }

  def name: Parser[String] = lower_word_or_integer | single_quoted
  def lower_word_or_integer: Parser[String] = """[a-z0-9_-][A-Za-z0-9_-]*""".r
  def single_quoted: Parser[String] = "'" ~> """[^']*""".r <~ "'"
  def integer: Parser[Int] = """\d+""".r ^^ { _.toInt }
}
