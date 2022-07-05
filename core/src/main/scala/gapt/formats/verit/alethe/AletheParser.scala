package gapt.formats.verit.alethe

import java.io.Reader
import java.io.StringReader
import scala.util.parsing.combinator.RegexParsers

case class AletheException( msg: String ) extends Exception {
  override def getMessage: String = msg
}

object parseAletheProof {

  def apply( in: String ): AletheProof =
    parseAletheProof( new StringReader( in ) )

  def apply( in: Reader ): AletheProof = {
    val parser = new AletheParser() {}
    parser.parseAll( parser.aletheProof, in ) match {
      case parser.Success( p: AletheProof, _ ) => p
      case e: parser.NoSuccess =>
        throw AletheException( s"Error parsing alethe proof: ${e}" )
    }
  }
}

trait AletheParser extends RegexParsers {

  def aletheProof: Parser[AletheProof] =
    rep( proofCommand ) ^^ { AletheProof }

  private def label: Parser[String] =
    """[A-Za-z0-9]+""".r

  private def proofCommand: Parser[ProofCommand] =
    assumption | step | anchor

  private def assumption: Parser[Assume] =
    "(" ~ "assume" ~> label ~ term <~ ")" ^^ {
      case l ~ f => Assume( l, f )
    }

  private def rule_name: Parser[String] =
    """[^ ():$]+""".r

  private def clause: Parser[List[Term]] =
    "(" ~ "cl" ~> rep( term ) <~ ")"

  private def step: Parser[Step] =
    "(" ~ "step" ~> symbol ~ clause ~
      ":rule" ~ rule_name ~
      premises ~
      arguments <~ ")" ^^ {
        case l ~ cl ~ _ ~ r ~ ps ~ as => Step(
          r, l, cl, ps.getOrElse( Nil ), as.getOrElse( Nil ) )
      }

  private def anchor: Parser[ProofCommand] =
    "(" ~ "anchor" ~ ":step" ~> symbol ~ ( anchor_arguments ? ) <~ ")" ^^ {
      case l ~ as => Anchor( l, as )
    }

  private def anchor_arguments: Parser[List[( VariableDeclaration, Term )]] =
    ":args" ~ "(" ~> rep1( anchor_argument ) <~ ")"

  private def anchor_argument: Parser[( VariableDeclaration, Term )] =
    "(" ~ ":=" ~> ( variable | sorted_var ) ~ term <~ ")" ^^ {
      case sym ~ t => sym -> t
    }

  private def variable: Parser[VariableDeclaration] =
    symbol ^^ { VariableDeclaration( _, None ) }

  private def premises: Parser[Option[List[String]]] =
    ( ":premises" ~ "(" ~> rep1( symbol ) <~ ")" ) ?

  private def arguments: Parser[Option[List[Argument]]] =
    ( ":args" ~> "(" ~> rep1( proof_argument ) <~ ")" ) ?

  private def symbol: Parser[String] = """[^ ():$]+""".r

  private def proof_argument: Parser[Argument] =
    term ^^ { Argument( _, None ) } |
      ( "(" ~> symbol ~ term <~ ")" ) ^^ {
        case v ~ t => Argument( t, Some( v ) )
      }

  private def variable_name: Parser[String] = symbol

  private def sort: Parser[Sort] =
    identifier ^^ { n => Sort( n ) }

  private val identifierRegexp = """[^ ():$]+""".r

  private val keywords = Set( "as", "forall", "exists", "let", "true", "false" )

  private def identifier: Parser[String] = Parser(
    input => identifierRegexp( input ).filterWithError(
      !keywords.contains( _ ),
      m => s"$m is a keyword",
      input ) )

  private def sorted_var: Parser[VariableDeclaration] =
    "(" ~> variable_name ~ sort <~ ")" ^^ {
      case v ~ s => VariableDeclaration( v, Some( s ) )
    }

  private def term: Parser[Term] = {
    negation |
      equality |
      complex_term |
      forall_term |
      exists_term |
      let_term |
      special_constant |
      qualified_identifier
  }

  private def let_term: Parser[Term] =
    "(" ~ "let" ~ "(" ~> rep1( binding ) ~ ")" ~ term <~ ")" ^^ {
      case _ ~ _ ~ t => Let( Nil, t )
    }

  private def binding: Parser[( String, Term )] = {
    "(" ~> variable_name ~ term <~ ")" ^^ { case v ~ t => ( v, t ) }
  }

  private def special_constant: Parser[SpecialConstant] =
    numeral | bool_true | bool_false

  private def bool_true: Parser[SpecialConstant] =
    "true" ^^ { _ => True }

  private def bool_false: Parser[SpecialConstant] =
    "false" ^^ { _ => False }

  private def qualified_identifier: Parser[Identifier] =
    identifier ^^ {
      n => Identifier( n, None )
    } | "(" ~ "as" ~> identifier ~ sort <~ ")" ^^ {
      case n ~ s => Identifier( n, Some( s ) )
    }

  private def numeral: Parser[Numeral] =
    ( "0" | """[1-9]\d*""".r ) ^^ {
      n => Numeral( n.toInt )
    }

  private def complex_term: Parser[Term] =
    "(" ~> identifier ~ rep1( term ) <~ ")" ^^ {
      case f ~ ts => Application( f, ts )
    }

  private def equality: Parser[Term] =
    "(" ~ "=" ~> term ~ term <~ ")" ^^ { case t1 ~ t2 => Application( "=", t1 :: t2 :: Nil ) }

  private def negation: Parser[Term] =
    "(" ~ "not" ~> term <~ ")" ^^ { t => Application( "not", t :: Nil ) }

  private def forall_term: Parser[Forall] =
    "(" ~ "forall" ~ "(" ~> rep( sorted_var ) ~ ")" ~ term <~ ")" ^^ {
      case vs ~ _ ~ f => println( "detected quantifier" ); Forall( vs, f )
    }

  private def exists_term: Parser[Exists] =
    "(" ~ "exists" ~ "(" ~> rep( sorted_var ) ~ ")" ~ term <~ ")" ^^ {
      case vs ~ _ ~ f => Exists( vs, f )
    }
}
