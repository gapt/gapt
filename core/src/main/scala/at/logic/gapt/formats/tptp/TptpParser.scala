package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._
import org.parboiled2._

import scala.util.{ Failure, Success }

class TptpParser( val input: ParserInput ) extends Parser {
  import CharPredicate._

  def Ws = rule {
    quiet( zeroOrMore( anyOf( " \t \n" ) |
      ( '%' ~ zeroOrMore( noneOf( "\n" ) ) ) |
      ( "/*" ~ not_star_slash ~ oneOrMore( "*" ) ~ "/" ) ) )
  }
  def not_star_slash = rule { ( noneOf( "*" ).* ~ oneOrMore( "*" ) ~ noneOf( "/*" ) ).* ~ noneOf( "*" ).* }
  def Comma = rule { "," ~ Ws }

  def TPTP_file: Rule1[TptpFile] = rule { Ws ~ TPTP_input.* ~ EOI ~> ( TptpFile( _ ) ) }

  def TPTP_input = rule { annotated_formula | include }

  def annotated_formula = rule {
    atomic_word ~ "(" ~ Ws ~ name ~ Comma ~ formula_role ~ Comma ~ formula ~ annotations ~ ")." ~ Ws ~>
      ( AnnotatedFormula( _, _, _, _, _ ) )
  }
  def formula_role = rule { atomic_word }
  def annotations = rule { ( Comma ~ general_term ).* }

  def formula = rule { logic_formula }
  def logic_formula: Rule1[HOLFormula] = rule { unitary_formula ~ ( binary_nonassoc_part | or_formula_part | and_formula_part ).? }
  def binary_nonassoc_part = rule { binary_connective ~ unitary_formula ~> ( ( a: HOLFormula, c: ( LambdaExpression, LambdaExpression ) => HOLFormula, b: HOLFormula ) => c( a, b ) ) }
  def or_formula_part = rule { ( "|" ~ Ws ~ unitary_formula ).+ ~> ( ( a: HOLFormula, as: Seq[HOLFormula] ) => Or.leftAssociative( a +: as: _* ) ) }
  def and_formula_part = rule { ( "&" ~ Ws ~ unitary_formula ).+ ~> ( ( a: HOLFormula, as: Seq[HOLFormula] ) => And.leftAssociative( a +: as: _* ) ) }
  def unitary_formula: Rule1[HOLFormula] = rule { quantified_formula | unary_formula | atomic_formula | "(" ~ Ws ~ logic_formula ~ ")" ~ Ws }
  def quantified_formula = rule { fol_quantifier ~ "[" ~ Ws ~ variable_list ~ "]" ~ Ws ~ ":" ~ Ws ~ unitary_formula ~> ( ( q: QuantifierHelper, vs, m ) => q.Block( vs, m ) ) }
  def variable_list = rule { variable.+.separatedBy( Comma ) }
  def unary_formula = rule { "~" ~ Ws ~ unitary_formula ~> ( Neg( _ ) ) }

  def atomic_formula = rule { defined_prop | infix_formula | plain_atomic_formula | ( distinct_object ~> ( FOLAtom( _ ) ) ) }
  def plain_atomic_formula = rule { atomic_word ~ ( "(" ~ Ws ~ arguments ~ ")" ~ Ws ).? ~> ( ( p, as ) => TptpAtom( p, as.getOrElse( Seq() ) ) ) }
  def defined_prop = rule { "$" ~ Ws ~ ( "true" ~ push( Top() ) | "false" ~ push( Bottom() ) ) ~ Ws }
  def infix_formula = rule { term ~ ( "=" ~ Ws ~ term ~> ( Eq( _: LambdaExpression, _ ) ) | "!=" ~ Ws ~ term ~> ( ( _: LambdaExpression ) !== _ ) ) }

  def fol_quantifier = rule { ( "!" ~ push( at.logic.gapt.expr.All ) | "?" ~ push( Ex ) ) ~ Ws }
  def binary_connective = rule {
    ( ( "<=>" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => a <-> b ) ) |
      ( "=>" ~ push( Imp( _: LambdaExpression, _: LambdaExpression ) ) ) |
      ( "<=" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => Imp( b, a ) ) ) |
      ( "<~>" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => -( a <-> b ) ) ) |
      ( "~|" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => -( a | b ) ) ) |
      ( "~&" ~ push( ( a: LambdaExpression, b: LambdaExpression ) => -( a & b ) ) ) ) ~ Ws
  }

  def term: Rule1[LambdaExpression] = rule { variable | ( distinct_object ~> ( FOLConst( _ ) ) ) | ( number ~> ( FOLConst( _ ) ) ) | function_term }
  def function_term = rule { name ~ ( "(" ~ Ws ~ term.+.separatedBy( Comma ) ~ ")" ~ Ws ).? ~> ( ( hd, as ) => TptpTerm( hd, as.getOrElse( Seq() ) ) ) }
  def variable = rule { capture( upper_word ) ~ Ws ~> ( FOLVar( _: String ) ) }
  def arguments = rule { term.+.separatedBy( Comma ) }

  def include = rule { "include(" ~ Ws ~ file_name ~ formula_selection ~ ")." ~ Ws ~> ( IncludeDirective( _, _ ) ) }
  def formula_selection = rule { ( "," ~ Ws ~ "[" ~ name.*.separatedBy( Comma ) ~ "]" ~ Ws ).? }

  def general_list: Rule1[Seq[LambdaExpression]] = rule { "[" ~ Ws ~ general_term.*.separatedBy( Comma ) ~ "]" ~ Ws }
  def general_terms = rule { general_term.+.separatedBy( Comma ) }
  def general_term: Rule1[LambdaExpression] = rule {
    general_data ~ ( ":" ~ Ws ~ general_term ).? ~> ( ( d, to ) => to.fold( d )( t => GeneralColon( d, t ) ) ) |
      general_list ~> ( GeneralList( _: Seq[LambdaExpression] ) )
  }
  def general_data: Rule1[LambdaExpression] = rule {
    formula_data | general_function | atomic_word ~> ( FOLConst( _ ) ) |
      variable | ( number ~> ( FOLConst( _ ) ) ) | ( distinct_object ~> ( FOLConst( _ ) ) )
  }
  def formula_data: Rule1[LambdaExpression] = rule {
    ( ( capture( "$" ~ ( "thf" | "tff" | "fof" | "cnf" ) ) ~ "(" ~ Ws ~ formula ~ ")" ~ Ws ) |
      ( capture( "$fot" ) ~ "(" ~ Ws ~ term ~ ")" ~ Ws ) ) ~> ( TptpTerm( _: String, _: LambdaExpression ) )
  }
  def general_function = rule { atomic_word ~ "(" ~ Ws ~ general_terms ~ ")" ~ Ws ~> ( TptpTerm( _, _ ) ) }

  def name: Rule1[String] = rule { atomic_word | integer }
  // We include defined words as atomic_word, since no prover can keep them apart...
  def atomic_word = rule { ( capture( lower_word ) ~ Ws ) | single_quoted }

  def number = rule { rational | real | integer }

  def file_name = rule { single_quoted }

  def single_quoted = rule { '\'' ~ sg_char.* ~ '\'' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

  def distinct_object = rule { '"' ~ do_char.* ~ '"' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

  val alpha_numeric = UpperAlpha ++ LowerAlpha ++ Digit ++ CharPredicate( "$_" )
  def upper_word = rule { UpperAlpha ~ alpha_numeric.* }
  def lower_word = rule { ( LowerAlpha ++ CharPredicate( "$_" ) ) ~ alpha_numeric.* }

  def real = rule { capture( anyOf( "+-" ).? ~ decimal ~ ( '.' ~ Digit.* ).? ~ ( anyOf( "Ee" ) ~ anyOf( "+-" ).? ~ decimal ).? ) ~ Ws }
  def rational = rule { capture( anyOf( "+-" ).? ~ decimal ~ '/' ~ positive_decimal ) ~ Ws }
  def integer = rule { capture( anyOf( "+-" ).? ~ decimal ) ~ Ws }
  def decimal = rule { '0' | positive_decimal }
  def positive_decimal = rule { Digit19 ~ Digit.* }

  val do_char_pred = CharPredicate( ' ' to '!', '#' to '[', '(' to '[', ']' to '~' )
  def do_char = rule { capture( do_char_pred ) | ( "\\\\" ~ push( "\\" ) ) | ( "\\\"" ~ push( "\"" ) ) }
  val sg_char_pred = CharPredicate( ' ' to '&', '(' to '[', ']' to '~' )
  def sg_char = rule { capture( sg_char_pred ) | ( "\\\\" ~ push( "\\" ) ) | ( "\\'" ~ push( "'" ) ) }
}

object TptpParser {
  def parseString( input: String, sourceName: String = "<string>" ): TptpFile = {
    val parser = new TptpParser( input )
    parser.TPTP_file.run() match {
      case Failure( error: ParseError ) =>
        throw new IllegalArgumentException( s"Parse error in $sourceName:\n" +
          parser.formatError( error, new ErrorFormatter( showTraces = true ) ) )
      case Failure( exception ) => throw exception
      case Success( value )     => value
    }
  }

  def parseFile( fileName: String ): TptpFile =
    parseString( io.Source.fromFile( fileName ).mkString, fileName )
  def loadFile( fileName: String ): TptpFile =
    resolveIncludes( TptpFile( Seq( IncludeDirective( fileName, None ) ) ), parseFile )

  def main( args: Array[String] ): Unit =
    print( loadFile( args.head ) )
}
