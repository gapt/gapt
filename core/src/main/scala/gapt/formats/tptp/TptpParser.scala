package gapt.formats.tptp

import gapt.expr._
import gapt.expr.preExpr.{ All => PreAll, And => PreAnd, Bottom => PreBottom, Eq => PreEq, Ex => PreEx, Expr => PreExpr, Ident => PreIdent, Iff => PreIff, Imp => PreImp, Neg => PreNeg, Or => PreOr, Top => PreTop, TypeAnnotation }
import gapt.expr.preExprHelper._
import gapt.formats.InputFile
import org.parboiled2._
import ammonite.ops._

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
  def Colon = rule { ":" ~ Ws }
  def TypeArrow = rule { ">" ~ Ws }
  def TypeProduct = rule { "*" ~ Ws }

  def TPTP_file: Rule1[TptpFile] = rule { Ws ~ TPTP_input.* ~ EOI ~> ( TptpFile( _ ) ) }

  def TPTP_input = rule { annotated_formula | type_declaration | annotated_preformula | include }

  def annotated_formula = rule {
    "fof(" ~ Ws ~ name ~ Comma ~ formula_role ~ Comma ~ formula ~ annotations ~ ")." ~ Ws ~>
      ( AnnotatedFormula( "fof", _, _, _, _ ) )
  }

  def type_declaration = rule {
    atomic_word ~ "(" ~ Ws ~ name ~ Comma ~ "type" ~ Comma ~ ( atomic_word | number ) ~ Ws ~ ":" ~ Ws ~ complex_type ~ annotations ~ ")." ~ Ws ~>
      ( TypeDeclaration( _, _, _, _, _ ) )
  }
  def annotated_preformula = rule {
    atomic_word ~ "(" ~ Ws ~ name ~ Comma ~ formula_role ~ Comma ~ pre_formula ~ annotations ~ ")." ~ Ws ~>
      ( AnnotatedPreFormula( _, _, _, _, _ ) )
  }

  def formula_role = rule { atomic_word }
  def annotations = rule { ( Comma ~ general_term ).* }

  // FOF formula
  def formula = rule { unitary_formula ~ ( binary_nonassoc_part | or_formula_part | and_formula_part ).? }
  def binary_nonassoc_part = rule { binary_connective ~ unitary_formula ~> ( ( a: Formula, c: ( Expr, Expr ) => Formula, b: Formula ) => c( a, b ) ) }
  def or_formula_part = rule { ( "|" ~ Ws ~ unitary_formula ).+ ~> ( ( a: Formula, as: Seq[Formula] ) => Or.leftAssociative( a +: as: _* ) ) }
  def and_formula_part = rule { ( "&" ~ Ws ~ unitary_formula ).+ ~> ( ( a: Formula, as: Seq[Formula] ) => And.leftAssociative( a +: as: _* ) ) }
  def unitary_formula: Rule1[Formula] = rule { quantified_formula | unary_formula | atomic_formula | "(" ~ Ws ~ formula ~ ")" ~ Ws }
  def quantified_formula = rule { fol_quantifier ~ "[" ~ Ws ~ variable_list ~ "]" ~ Ws ~ ":" ~ Ws ~ unitary_formula ~> ( ( q: QuantifierHelper, vs, m ) => q.Block( vs, m ) ) }
  def variable_list = rule { ( variable ~ ( ":" ~ Ws ~ name ).? ~> ( ( a, b ) => a ) ).+.separatedBy( Comma ) }
  def unary_formula = rule { "~" ~ Ws ~ unitary_formula ~> ( Neg( _ ) ) }

  def atomic_formula = rule { defined_prop | infix_formula | plain_atomic_formula | ( distinct_object ~> ( FOLAtom( _ ) ) ) }
  def plain_atomic_formula = rule { atomic_word ~ ( "(" ~ Ws ~ arguments ~ ")" ~ Ws ).? ~> ( ( p, as ) => TptpAtom( p, as.getOrElse( Seq() ) ) ) }
  def defined_prop = rule { "$" ~ Ws ~ ( "true" ~ push( Top() ) | "false" ~ push( Bottom() ) ) ~ Ws }
  def infix_formula = rule { term ~ ( "=" ~ Ws ~ term ~> ( Eq( _: Expr, _ ) ) | "!=" ~ Ws ~ term ~> ( ( _: Expr ) !== _ ) ) }

  def fol_quantifier = rule { ( "!" ~ push( gapt.expr.All ) | "?" ~ push( Ex ) ) ~ Ws }
  def binary_connective = rule {
    ( ( "<=>" ~ push( ( a: Expr, b: Expr ) => a <-> b ) ) |
      ( "=>" ~ push( Imp( _: Expr, _: Expr ) ) ) |
      ( "<=" ~ push( ( a: Expr, b: Expr ) => Imp( b, a ) ) ) |
      ( "<~>" ~ push( ( a: Expr, b: Expr ) => -( a <-> b ) ) ) |
      ( "~|" ~ push( ( a: Expr, b: Expr ) => -( a | b ) ) ) |
      ( "~&" ~ push( ( a: Expr, b: Expr ) => -( a & b ) ) ) ) ~ Ws
  }

  def term: Rule1[Expr] = rule { variable | ( distinct_object ~> ( FOLConst( _ ) ) ) | ( number ~> ( FOLConst( _ ) ) ) | function_term }
  def function_term = rule { name ~ ( "(" ~ Ws ~ term.+.separatedBy( Comma ) ~ ")" ~ Ws ).? ~> ( ( hd, as ) => TptpTerm( hd, as.getOrElse( Seq() ) ) ) }
  def variable = rule { capture( upper_word ) ~ Ws ~> ( FOLVar( _: String ) ) }
  def arguments = rule { term.+.separatedBy( Comma ) }

  //TFF pre-formula (typing must be performed afterwards)
  def pre_formula: Rule1[PreExpr] = rule { pre_unitary_formula ~ ( pre_binary_nonassoc_part | pre_or_formula_part | pre_and_formula_part ).? }
  def pre_binary_nonassoc_part = rule { pre_binary_connective ~ pre_unitary_formula ~> ( ( a: PreExpr, c: ( PreExpr, PreExpr ) => PreExpr, b: PreExpr ) => c( a, b ) ) }
  def pre_or_formula_part = rule { ( "|" ~ Ws ~ pre_unitary_formula ).+ ~> ( ( a: PreExpr, as: Seq[PreExpr] ) => OrLeftAssociative( a +: as: _* ) ) }
  def pre_and_formula_part = rule { ( "&" ~ Ws ~ pre_unitary_formula ).+ ~> ( ( a: PreExpr, as: Seq[PreExpr] ) => AndLeftAssociative( a +: as: _* ) ) }
  def pre_unitary_formula: Rule1[PreExpr] = rule { pre_quantified_formula | pre_unary_formula | pre_atomic_formula | "(" ~ Ws ~ pre_formula ~ ")" ~ Ws }
  def pre_quantified_formula = rule { pre_fol_quantifier ~ "[" ~ Ws ~ pre_variable_list ~ "]" ~ Ws ~ ":" ~ Ws ~ pre_unitary_formula ~> ( ( q: ( Seq[PreIdent], PreExpr ) => PreExpr, vs, m ) => q( vs, m ) ) }
  def pre_variable_list =
    rule {
      ( pre_variable ~ ( ":" ~ Ws ~ complex_type ).? ~> ( ( a: PreIdent, b: Option[preExpr.Type] ) => b match {
        case None       => PreIdent( a.name, preExpr.BaseType( "$i", Nil ), None )
        case Some( ty ) => PreIdent( a.name, ty, None ) //TODO: fix type parameters
      } ) ).+.separatedBy( Comma )
    }
  def pre_unary_formula = rule { "~" ~ Ws ~ pre_unitary_formula ~> ( PreNeg( _ ) ) }

  def pre_atomic_formula = rule { pre_defined_prop | pre_infix_formula | pre_plain_atomic_formula | ( distinct_object ~> ( PreIdent( _, preExpr.freshMetaType(), None ) ) ) }
  def pre_plain_atomic_formula = rule { atomic_word ~ ( "(" ~ Ws ~ pre_arguments ~ ")" ~ Ws ).? ~> ( ( p, as ) => PreApps( p, as.getOrElse( Seq() ) ) ) }
  def pre_defined_prop = rule { "$" ~ Ws ~ ( "true" ~ push( PreTop ) | "false" ~ push( PreBottom ) ) ~ Ws }
  def pre_infix_formula = rule { pre_term ~ ( "=" ~ Ws ~ pre_term ~> ( PreEq( _: PreExpr, _ ) ) | "!=" ~ Ws ~ pre_term ~> ( ( s: PreExpr, t: PreExpr ) => PreNeg( PreEq( s, t ) ) ) ) }

  def pre_fol_quantifier = rule { ( "!" ~ push( AllBlock ) | "?" ~ push( ExBlock ) ) ~ Ws }
  def pre_binary_connective = rule {
    ( ( "<=>" ~ push( ( a: PreExpr, b: PreExpr ) => PreIff( a, b ) ) ) |
      ( "=>" ~ push( PreImp( _: PreExpr, _: PreExpr ) ) ) |
      ( "<=" ~ push( ( a: PreExpr, b: PreExpr ) => PreImp( b, a ) ) ) |
      ( "<~>" ~ push( ( a: PreExpr, b: PreExpr ) => PreNeg( PreIff( a, b ) ) ) ) |
      ( "~|" ~ push( ( a: PreExpr, b: PreExpr ) => PreNeg( PreOr( a, b ) ) ) ) |
      ( "~&" ~ push( ( a: PreExpr, b: PreExpr ) => PreNeg( PreAnd( a, b ) ) ) ) ) ~ Ws
  }

  def pre_term: Rule1[PreExpr] = rule { pre_variable | ( distinct_object ~> ( PreIdent( _, preExpr.freshMetaType(), None ) ) ) | ( number ~> ( PreIdent( _, preExpr.freshMetaType(), None ) ) ) | pre_function_term }
  def pre_function_term = rule { name ~ ( "(" ~ Ws ~ pre_term.+.separatedBy( Comma ) ~ ")" ~ Ws ).? ~> ( ( hd, as ) => PreApps( hd, as.getOrElse( Seq() ) ) ) }
  def pre_variable = rule { capture( upper_word ) ~ Ws ~> ( PreIdent( _: String, preExpr.freshMetaType(), None ) ) }
  def pre_arguments = rule { pre_term.+.separatedBy( Comma ) }

  def include = rule { "include(" ~ Ws ~ file_name ~ formula_selection ~ ")." ~ Ws ~> ( IncludeDirective( _, _ ) ) }
  def formula_selection = rule { ( "," ~ Ws ~ "[" ~ name.*.separatedBy( Comma ) ~ "]" ~ Ws ).? }

  def general_list: Rule1[Seq[Expr]] = rule { "[" ~ Ws ~ general_term.*.separatedBy( Comma ) ~ "]" ~ Ws }
  def general_terms = rule { general_term.+.separatedBy( Comma ) }
  def general_term: Rule1[Expr] = rule {
    general_data ~ ( ":" ~ Ws ~ general_term ).? ~> ( ( d, to ) => to.fold( d )( t => GeneralColon( d, t ) ) ) |
      general_list ~> ( GeneralList( _: Seq[Expr] ) )
  }
  def general_data: Rule1[Expr] = rule {
    formula_data | general_function | atomic_word ~> ( FOLConst( _ ) ) |
      variable | ( number ~> ( FOLConst( _ ) ) ) | ( distinct_object ~> ( FOLConst( _ ) ) )
  }
  def formula_data: Rule1[Expr] = rule {
    ( ( capture( "$" ~ ( "thf" | "tff" | "fof" | "cnf" ) ) ~ "(" ~ Ws ~ formula ~ ")" ~ Ws ) |
      ( capture( "$fot" ) ~ "(" ~ Ws ~ term ~ ")" ~ Ws ) ) ~> ( TptpTerm( _: String, _: Expr ) )
  }
  def general_function = rule { atomic_word ~ "(" ~ Ws ~ general_terms ~ ")" ~ Ws ~> ( TptpTerm( _, _ ) ) }

  def name: Rule1[String] = rule { atomic_word | integer }
  // We include defined words as atomic_word, since no prover can keep them apart...
  def atomic_word = rule { ( capture( lower_word ) ~ Ws ) | single_quoted }

  def number = rule { rational | real | integer }

  def file_name = rule { single_quoted }

  def single_quoted = rule { '\'' ~ sg_char.* ~ '\'' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

  def distinct_object: Rule1[String] = rule { '"' ~ do_char.* ~ '"' ~ Ws ~> ( ( l: Seq[String] ) => l.mkString ) }

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

  def complex_type: Rule1[preExpr.Type] = rule { product_type | arrow_type }
  def arrow_type = rule { unitary_type.+.separatedBy( TypeArrow ) ~> { ( x: Seq[preExpr.Type] ) => x.reduceRight( preExpr.ArrType( _, _ ) ) } }
  def product_type = rule {
    // "($i)>$i" is handled by arrow_type
    "(" ~ unitary_type ~ Ws ~ TypeProduct ~ ( unitary_type.+.separatedBy( TypeProduct ) ) ~ ")" ~ Ws ~ TypeArrow ~ unitary_type ~>
      ( ( x, xs, t ) => ( x +: xs ).foldRight( t )( preExpr.ArrType( _, _ ) ) )
  }
  def unitary_type = rule { basic_type | "(" ~ complex_type ~ ")" ~ Ws }
  def basic_type = rule { //TODO: fix number typing
    atomic_word ~ ( "(" ~ Ws ~ complex_type.+.separatedBy( Comma ) ~ ")" ).? ~ Ws ~> {
      ( _, _ ) match {
        case ( "$o", _ )       => preExpr.BaseType( "o", Nil )
        case ( "$i", _ )       => preExpr.BaseType( "i", Nil )
        //TODO: rename types of o / i to something else?
        case ( name, optargs ) => preExpr.BaseType( name, optargs.map( _.toList ).getOrElse( Nil ) )
      }
    }
  }
}

object TptpParser {
  /**
   * Parse a TPTP file, but do not resolve include directives.
   */
  def parse( file: InputFile ): TptpFile = {
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
   * The default resolver looks for include files relative to the current working directory
   * @param fileName the file name
   * @return the parsed tptp (include) file
   */
  def default_resolver( fileName: String ) = parse( FilePath( fileName ) )

  /**
   * Load a TPTP file resolving includes.
   * @param file the input file to load
   * @param resolver a function used to resolve eventual included files
   * @return the parsed file
   */
  def load( file: InputFile, resolver: String => TptpFile = default_resolver ): TptpFile =
    resolveIncludes( parse( file ), resolver )

  def main( args: Array[String] ): Unit =
    print( load( FilePath( args.head ) ) )

}

