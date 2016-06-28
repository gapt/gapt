package at.logic.gapt.formats.nanocop
import at.logic.gapt.expr.{ FOLAtom, FOLConst, FOLFunction, FOLTerm, FOLVar }
import org.parboiled2._

import scala.util.{ Failure, Success }

class NanocopParser( val input: ParserInput ) extends Parser {

  def Ws = rule { quiet( zeroOrMore( anyOf( " \n" ) ) ) }

  def File = rule { Ws ~ Children ~ Children ~ EOI ~> ( ( _, _ ) ) }

  def Children: Rule1[Seq[NanocopProof]] = rule { "[" ~ Ws ~ zeroOrMore( Proof ~> ( Seq( _ ) ) | Children ).separatedBy( "," ~ Ws ) ~ "]" ~ Ws ~> ( ( _: Seq[Seq[NanocopProof]] ).flatten ) }

  def Proof: Rule1[NanocopProof] =
    rule { Matrix | Clause | Atom }

  def Clause = rule { "(" ~ Ws ~ Num ~ "^" ~ Ws ~ Num ~ ")" ~ Ws ~ "^" ~ Ws ~ Terms ~ ":" ~ Ws ~ Children ~> NanocopClause }
  def Terms = rule { "[" ~ Ws ~ zeroOrMore( Term ).separatedBy( "," ~ Ws ) ~ "]" ~ Ws }

  def Matrix = rule { Num ~ "^" ~ Ws ~ Num ~ ":" ~ Ws ~ Children ~> NanocopMatrix }

  def Atom: Rule1[NanocopAtom] = rule {
    "-" ~ Ws ~ "(" ~ Atom ~ ")" ~> ( _.copy( pol = false ) ) |
      Word ~ optional( "(" ~ Ws ~ oneOrMore( Term ).separatedBy( "," ~ Ws ) ~ ")" ~ Ws ) ~>
      ( ( hd: String, args: Option[Seq[FOLTerm]] ) => NanocopAtom( args.fold( FOLAtom( hd ) )( FOLAtom( hd, _ ) ), true ) )
  }

  def Term: Rule1[FOLTerm] = rule {
    Variable |
      Word ~ optional( "(" ~ Ws ~ oneOrMore( Term ).separatedBy( "," ~ Ws ) ~ ")" ~ Ws ) ~>
      ( ( hd: String, args: Option[Seq[FOLTerm]] ) => args.fold( FOLFunction( hd ) )( FOLFunction( hd, _ ) ) )
  }

  val WordChar = CharPredicate.AlphaNum ++ CharPredicate( '_' )
  def Word = rule { capture( oneOrMore( WordChar ) ) ~ Ws }

  def Variable = rule { capture( "_" ~ oneOrMore( CharPredicate.Digit ) ) ~ Ws ~> ( FOLVar( _ ) ) }

  def Num = rule { optional( "_" ) ~ capture( oneOrMore( CharPredicate.Digit ) ) ~ Ws ~> ( _.toInt ) }

}
object NanocopParser {
  def parseString( input: String, sourceName: String = "<string>" ): ( Seq[NanocopProof], Seq[NanocopProof] ) = {
    val parser = new NanocopParser( input )
    parser.File.run() match {
      case Failure( error: ParseError ) =>
        throw new IllegalArgumentException( s"Parse error in $sourceName:\n" +
          parser.formatError( error, new ErrorFormatter( showTraces = true ) ) )
      case Failure( exception ) => throw exception
      case Success( value )     => value
    }
  }
}
