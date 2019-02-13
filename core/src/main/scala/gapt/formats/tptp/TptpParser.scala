package gapt.formats.tptp

import gapt.expr._
import gapt.formats.InputFile
import org.parboiled2._
import ammonite.ops._
import gapt.expr.ty.TBase
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.ty.Ty

import scala.util.{ Failure, Success }

class TptpParser( val input: ParserInput ) extends Parser {
  import CharPredicate._

  private def Ws = rule {
    quiet( zeroOrMore( anyOf( " \t \n" ) |
      ( '%' ~ zeroOrMore( noneOf( "\n" ) ) ) |
      ( "/*" ~ not_star_slash ~ oneOrMore( "*" ) ~ "/" ) ) )
  }
  private def not_star_slash = rule { ( noneOf( "*" ).* ~ oneOrMore( "*" ) ~ noneOf( "/*" ) ).* ~ noneOf( "*" ).* }
  private def Comma = rule { "," ~ Ws }
  private def Colon = rule { ":" ~ Ws }

  def TPTP_file: Rule1[TptpFile] = rule { Ws ~ TPTP_input.* ~ EOI ~> ( TptpFile( _ ) ) }

  private def TPTP_input = rule { annotated_formula | include }

  private def annotated_formula = rule {
    atomic_word ~ "(" ~ Ws ~ name ~ Comma ~ formula_role ~ Comma ~ formula ~ annotations ~ ")." ~ Ws ~>
      ( AnnotatedFormula( _, _, _, _, _ ) )
  }
  private def formula_role = rule { atomic_word }
  private def annotations = rule { ( Comma ~ general_term ).* }

  private def formula = rule { typed_logic_formula }
  private def typed_logic_formula = rule { logic_formula } //add type annotation
  private def logic_formula: Rule1[Formula] = rule { unitary_formula ~ ( binary_nonassoc_part | or_formula_part | and_formula_part ).? }
  private def binary_nonassoc_part = rule { binary_connective ~ unitary_formula ~> ( ( a: Formula, c: ( Expr, Expr ) => Formula, b: Formula ) => c( a, b ) ) }
  private def or_formula_part = rule { ( "|" ~ Ws ~ unitary_formula ).+ ~> ( ( a: Formula, as: Seq[Formula] ) => Or.leftAssociative( a +: as: _* ) ) }
  private def and_formula_part = rule { ( "&" ~ Ws ~ unitary_formula ).+ ~> ( ( a: Formula, as: Seq[Formula] ) => And.leftAssociative( a +: as: _* ) ) }
  private def unitary_formula: Rule1[Formula] = rule { quantified_formula | unary_formula | atomic_formula | "(" ~ Ws ~ logic_formula ~ ")" ~ Ws }
  private def quantified_formula = rule { fol_quantifier ~ "[" ~ Ws ~ variable_list ~ "]" ~ Ws ~ ":" ~ Ws ~ unitary_formula ~> ( ( q: QuantifierHelper, vs, m ) => q.Block( vs, m ) ) }
  private def variable_list = rule { ( variable ~ ( ":" ~ Ws ~ name ).? ~> ( ( a, b ) => a ) ).+.separatedBy( Comma ) }
  private def unary_formula = rule { "~" ~ Ws ~ unitary_formula ~> ( Neg( _ ) ) }

  private def atomic_formula = rule { defined_prop | infix_formula | plain_atomic_formula | ( distinct_object ~> ( FOLAtom( _ ) ) ) }
  private def plain_atomic_formula = rule { atomic_word ~ ( "(" ~ Ws ~ arguments ~ ")" ~ Ws ).? ~> ( ( p, as ) => TptpAtom( p, as.getOrElse( Seq() ) ) ) }
  private def defined_prop = rule { "$" ~ Ws ~ ( "true" ~ push( Top() ) | "false" ~ push( Bottom() ) ) ~ Ws }
  private def infix_formula = rule { term ~ ( "=" ~ Ws ~ term ~> ( Eq( _: Expr, _ ) ) | "!=" ~ Ws ~ term ~> ( ( _: Expr ) !== _ ) ) }

  private def fol_quantifier = rule { ( "!" ~ push( gapt.expr.All ) | "?" ~ push( Ex ) ) ~ Ws }
  private def binary_connective = rule {
    ( ( "<=>" ~ push( ( a: Expr, b: Expr ) => a <-> b ) ) |
      ( "=>" ~ push( Imp( _: Expr, _: Expr ) ) ) |
      ( "<=" ~ push( ( a: Expr, b: Expr ) => Imp( b, a ) ) ) |
      ( "<~>" ~ push( ( a: Expr, b: Expr ) => -( a <-> b ) ) ) |
      ( "~|" ~ push( ( a: Expr, b: Expr ) => -( a | b ) ) ) |
      ( "~&" ~ push( ( a: Expr, b: Expr ) => -( a & b ) ) ) ) ~ Ws
  }

  private def term: Rule1[Expr] = rule { variable | ( distinct_object ~> ( FOLConst( _ ) ) ) | ( number ~> ( FOLConst( _ ) ) ) | function_term }
  private def function_term = rule { name ~ ( "(" ~ Ws ~ term.+.separatedBy( Comma ) ~ ")" ~ Ws ).? ~> ( ( hd, as ) => TptpTerm( hd, as.getOrElse( Seq() ) ) ) }
  private def variable = rule { capture( upper_word ) ~ Ws ~> ( FOLVar( _: String ) ) }
  private def arguments = rule { term.+.separatedBy( Comma ) }

  private def include = rule { "include(" ~ Ws ~ file_name ~ formula_selection ~ ")." ~ Ws ~> ( IncludeDirective( _, _ ) ) }
  private def formula_selection = rule { ( "," ~ Ws ~ "[" ~ name.*.separatedBy( Comma ) ~ "]" ~ Ws ).? }

  private def general_list: Rule1[Seq[Expr]] = rule { "[" ~ Ws ~ general_term.*.separatedBy( Comma ) ~ "]" ~ Ws }
  private def general_terms = rule { general_term.+.separatedBy( Comma ) }
  private def general_term: Rule1[Expr] = rule {
    general_data ~ ( ":" ~ Ws ~ general_term ).? ~> ( ( d, to ) => to.fold( d )( t => GeneralColon( d, t ) ) ) |
      general_list ~> ( GeneralList( _: Seq[Expr] ) )
  }
  private def general_data: Rule1[Expr] = rule {
    formula_data | general_function | atomic_word ~> ( FOLConst( _ ) ) |
      variable | ( number ~> ( FOLConst( _ ) ) ) | ( distinct_object ~> ( FOLConst( _ ) ) )
  }
  private def formula_data: Rule1[Expr] = rule {
    ( ( capture( "$" ~ ( "thf" | "tff" | "fof" | "cnf" ) ) ~ "(" ~ Ws ~ formula ~ ")" ~ Ws ) |
      ( capture( "$fot" ) ~ "(" ~ Ws ~ term ~ ")" ~ Ws ) ) ~> ( TptpTerm( _: String, _: Expr ) )
  }
  private def general_function = rule { atomic_word ~ "(" ~ Ws ~ general_terms ~ ")" ~ Ws ~> ( TptpTerm( _, _ ) ) }

  private def name: Rule1[String] = rule { atomic_word | integer }
  // We include defined words as atomic_word, since no prover can keep them apart...
  private def atomic_word = rule { ( capture( lower_word ) ~ Ws ) | single_quoted }

  private def number = rule { rational | real | integer }

  private def file_name = rule { single_quoted }

  private def single_quoted = rule { '\'' ~ sg_char.* ~ '\'' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

  private def distinct_object = rule { '"' ~ do_char.* ~ '"' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

  private val alpha_numeric = UpperAlpha ++ LowerAlpha ++ Digit ++ CharPredicate( "$_" )
  private def upper_word = rule { UpperAlpha ~ alpha_numeric.* }
  private def lower_word = rule { ( LowerAlpha ++ CharPredicate( "$_" ) ) ~ alpha_numeric.* }

  private def real = rule { capture( anyOf( "+-" ).? ~ decimal ~ ( '.' ~ Digit.* ).? ~ ( anyOf( "Ee" ) ~ anyOf( "+-" ).? ~ decimal ).? ) ~ Ws }
  private def rational = rule { capture( anyOf( "+-" ).? ~ decimal ~ '/' ~ positive_decimal ) ~ Ws }
  private def integer = rule { capture( anyOf( "+-" ).? ~ decimal ) ~ Ws }
  private def decimal = rule { '0' | positive_decimal }
  private def positive_decimal = rule { Digit19 ~ Digit.* }

  private val do_char_pred = CharPredicate( ' ' to '!', '#' to '[', '(' to '[', ']' to '~' )
  private def do_char = rule { capture( do_char_pred ) | ( "\\\\" ~ push( "\\" ) ) | ( "\\\"" ~ push( "\"" ) ) }
  private val sg_char_pred = CharPredicate( ' ' to '&', '(' to '[', ']' to '~' )
  private def sg_char = rule { capture( sg_char_pred ) | ( "\\\\" ~ push( "\\" ) ) | ( "\\'" ~ push( "'" ) ) }

  private def complex_type = rule { basic_type | ( ">" ~ push( ( t1: Ty, t2: Ty ) => t1 -> t2 ) ) }
  private def basic_type = rule {
    atomic_word ~> ( name =>
      name match {
        case "$o" => To
        case "$i" => Ti
        case name => TBase( name )
      } )
  }
}

object TptpImporter {
  /**
   * Parse a TPTP file, but do not resolve include directives.
   */
  private def parse( file: InputFile ): TptpFile = {
    val input = file.read
    val parser = new TptpParser( input )
    parser.TPTP_file.run() match {
      case Failure( error: ParseError ) =>
        throw new IllegalArgumentException( s"Parse error in ${file.fileName}:\n" +
          parser.formatError( error, new ErrorFormatter( showTraces = true ) ) )
      case Failure( exception ) => throw exception
      case Success( value )     => value
    }
  }

  /**
   * Load a TPTP file, but don't resolve includes.
   * @param file The input file to load.
   * @return The parsed file.
   */
  def loadWithoutIncludes( file: InputFile ): TptpFile = parse( file )

  /**
   * Load a TPTP file and resolve includes.
   * @param file The input file to load.
   * @param resolver How to resolve included files.
   * @return The parsed file.
   */
  def loadWithIncludes( file: InputFile, resolver: String => TptpFile ): TptpFile =
    resolveIncludes( parse( file ), resolver )

  def loadWithIncludes( file: InputFile, relativeTo: Path ): TptpFile =
    loadWithIncludes( file, fileName => parse( Path( fileName, relativeTo ) ) )

  def loadWithIncludes( file: InputFile, relativeTo: FilePath ): TptpFile =
    loadWithIncludes( file, Path( relativeTo, pwd ) )

  def loadWithIncludes( file: InputFile, relativeTo: String ): TptpFile =
    loadWithIncludes( file, FilePath( relativeTo ) )

  def loadWithIncludes( file: InputFile ): TptpFile =
    loadWithIncludes( file, pwd )

  def main( args: Array[String] ): Unit =
    print( loadWithIncludes( FilePath( args.head ) ) )

}
