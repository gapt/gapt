package at.logic.gapt.formats.babel

import at.logic.gapt.{ expr => real }
import at.logic.gapt.expr.{ Formula, Expr, preExpr }
import at.logic.gapt.proofs.gaptic.guessLabels
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.utils.NameGenerator
import fastparse.StringReprOps
import fastparse.core.ParseError
import fastparse.utils.IndexedParserInput
import cats.syntax.either._

sealed abstract class BabelParseError( message: String ) extends IllegalArgumentException( message )
case class BabelElabError( reason: String ) extends BabelParseError( reason )
case class BabelParsingError( parseError: fastparse.all.Parsed.Failure ) extends BabelParseError( ParseError( parseError ).getMessage )

object BabelLexical {
  import fastparse.all._

  val Whitespace = NoTrace( CharsWhile( _.isWhitespace, min = 0 ) )

  val Name: P[String] = P( UnquotedName | QuotedName )
  def isUnquotNameChar( c: Char ) = ( c.isLetterOrDigit || c == '_' || c == '$' ) && c != 'λ'
  val UnquotedName: P[String] = P( CharsWhile( isUnquotNameChar ).! )
  val QuotedName: P[String] = P( "'" ~ QuotedNameChar.rep ~ "'" ).map( _.mkString )
  val QuotedNameChar: P[String] = P(
    CharsWhile( c => c != '\\' && c != '\'' ).! |
      ( "\\" ~ ( "'" | "\\" ).! ) |
      ( "\\u" ~ CharIn( ( 'a' to 'f' ) ++ ( '0' to '9' ) ).
        rep( min = 4, max = 4 ).!.
        map( Integer.parseInt( _, 16 ).toChar.toString ) ) )

  val keywords = Set( "true", "false", "all", "exists" )

  def kw( name: String ) = P( name ~ !CharPred( isUnquotNameChar ) )
}

object BabelParserCombinators {
  import BabelLexical._
  import fastparse.noApi._
  val White = fastparse.WhitespaceApi.Wrapper( Whitespace )
  import White._

  def MarkPos( p: P[preExpr.Expr] ): P[preExpr.Expr] =
    ( Index ~ p ~ Index ).map {
      case ( _, e @ preExpr.LocAnnotation( _, _ ), _ ) => e
      case ( begin, e, end ) =>
        preExpr.LocAnnotation( e, preExpr.Location( begin, end ) )
    }

  def PE( p: => P[preExpr.Expr] )( implicit name: sourcecode.Name ): P[preExpr.Expr] =
    P( MarkPos( p ) )( name )

  val ExprAndNothingElse: P[preExpr.Expr] = P( "" ~ Expr ~ End )
  val ConstAndNothingElse: P[real.Const] = P( "" ~ Const ~ End )

  val Expr: P[preExpr.Expr] = P( Lam )

  val BoundVar: P[preExpr.Ident] = P( Ident | ( "(" ~ Name ~ ":" ~ Type ~ ")" ).map( x => preExpr.Ident( x._1, x._2 ) ) )
  val Lam: P[preExpr.Expr] = PE( ( ( "^" | "λ" ) ~/ BoundVar ~ Lam ).map( x => preExpr.Abs( x._1, x._2 ) ) | TypeAnnotation )

  val TypeAnnotation: P[preExpr.Expr] = PE( ( Impl ~/ ( ":" ~ Type ).? ) map {
    case ( expr, Some( ty ) ) => preExpr.TypeAnnotation( expr, ty )
    case ( expr, None )       => expr
  } )

  val Impl = PE( Bicond.rep( 1, "->" | "⊃" ).map( _.reduceRight( preExpr.Imp ) ) )
  val Bicond = PE( Disj.rep( 1, "<->" ).map {
    case Seq( formula ) => formula
    case formulas       => ( formulas, formulas.tail ).zipped.map( preExpr.Bicond ).reduceLeft( preExpr.And )
  } )

  val Disj = PE( Conj.rep( 1, "|" | "∨" ).map( _.reduceLeft( preExpr.Or ) ) )

  val Conj = PE( QuantOrNeg.rep( 1, "&" | "∧" ).map( _.reduceLeft( preExpr.And ) ) )

  val QuantOrNeg: P[preExpr.Expr] = P( Ex | All | Neg | InfixRel )
  val Ex = PE( ( ( "?" | "∃" ) ~/ BoundVar ~ QuantOrNeg ).map( preExpr.Ex.tupled ) )
  val All = PE( ( ( "!" | "∀" ) ~/ BoundVar ~ QuantOrNeg ).map( preExpr.All.tupled ) )
  val Neg = PE( ( ( "-" | "¬" ) ~ QuantOrNeg ).map( preExpr.Neg ) )

  val InfixRelSym = P( "<=" | ">=" | "<" | ">" | "=" | "!=" )
  val InfixRel = PE( ( PlusMinus ~/ ( InfixRelSym.! ~ PlusMinus ).rep ) map {
    case ( first, Seq() ) => first
    case ( first, conds ) =>
      val terms = first +: conds.map { _._2 }
      val rels = conds.map { _._1 }
      ( terms, rels, terms.tail ).zipped.map {
        case ( a, "!=", b ) => preExpr.Neg( preExpr.Eq( a, b ) )
        case ( a, "=", b )  => preExpr.Eq( a, b )
        case ( a, r, b ) =>
          preExpr.TypeAnnotation( preExpr.App( preExpr.App( preExpr.Ident( r, preExpr.freshMetaType() ), a ), b ), preExpr.Bool )
      }.reduceLeft( preExpr.And )
  } )

  val PlusMinus = PE( ( TimesDiv ~/ ( ( "+" | "-" ).! ~ TimesDiv ).rep ) map {
    case ( first, rest ) =>
      rest.foldLeft( first ) { case ( a, ( o, b ) ) => preExpr.App( preExpr.App( preExpr.Ident( o, preExpr.freshMetaType() ), a ), b ) }
  } )

  val TimesDiv = PE( ( App ~/ ( ( "*" | "/" ).! ~ App ).rep ) map {
    case ( first, rest ) =>
      rest.foldLeft( first ) { case ( a, ( o, b ) ) => preExpr.App( preExpr.App( preExpr.Ident( o, preExpr.freshMetaType() ), a ), b ) }
  } )

  val Tuple: P[Seq[preExpr.Expr]] = P( "(" ~/ Expr.rep( sep = "," ) ~ ")" )
  val App = PE( ( Atom ~/ ( Tuple | Atom.map( Seq( _ ) ) ).rep ) map {
    case ( expr, args ) => args.flatten.foldLeft( expr )( preExpr.App )
  } )

  val Parens = PE( "(" ~/ Expr ~/ ")" )
  val Atom = PE( Parens | True | False | VarLiteral | ConstLiteral | Ident )

  val True = PE( ( kw( "true" ) | "⊤" ).map( _ => preExpr.Top ) )
  val False = PE( ( kw( "false" ) | "⊥" ).map( _ => preExpr.Bottom ) )

  val Var = P( Name ~ ":" ~ Type ) map {
    case ( name, ty ) => real.Var( name, preExpr.toRealType( ty, Map() ) )
  }
  val Const = P( Name ~ ":" ~ Type ) map {
    case ( name, ty ) => real.Const( name, preExpr.toRealType( ty, Map() ) )
  }
  val VarLiteral = PE( ( "#v(" ~/ Var ~ ")" ).map { preExpr.QuoteBlackbox } )
  val ConstLiteral = PE( ( "#c(" ~/ Const ~ ")" ).map { preExpr.QuoteBlackbox } )

  val Ident: P[preExpr.Ident] = P( Name.map( preExpr.Ident( _, preExpr.freshMetaType() ) ) )

  val TypeParens: P[preExpr.Type] = P( "(" ~/ Type ~ ")" )
  val TypeBase: P[preExpr.Type] = P( Name ~ TypeAtom.rep ).map { case ( n, ps ) => preExpr.BaseType( n, ps.toList ) }
  val TypeVar: P[preExpr.Type] = P( "?" ~/ Name ).map( preExpr.VarType )
  val TypeAtom: P[preExpr.Type] = P( TypeParens | TypeVar | TypeBase )
  val Type: P[preExpr.Type] = P( TypeAtom.rep( min = 1, sep = ">" ) ).map { _.reduceRight( preExpr.ArrType ) }
  val TypeAndNothingElse = P( "" ~ Type ~ End )

  val Sequent = P( Expr.rep( sep = "," ) ~ ( ":-" | "⊢" ) ~ Expr.rep( sep = "," ) ).
    map { case ( ant, suc ) => HOLSequent( ant, suc ) }
  val SequentAndNothingElse = P( "" ~ Sequent ~ End )

  val LabelledFormula = P( ( Name ~ ":" ~ !"-" ).? ~ Expr )
  val LabelledSequent = P( LabelledFormula.rep( sep = "," ) ~ ( ":-" | "⊢" ) ~ LabelledFormula.rep( sep = "," ) ).
    map { case ( ant, suc ) => HOLSequent( ant, suc ) }
  val LabelledSequentAndNothingElse = P( "" ~ LabelledSequent ~ End )
}

object BabelParser {
  import BabelParserCombinators._
  import fastparse.all._

  private def ppElabError( text: String, err: preExpr.ElabError )( implicit sig: BabelSignature ): BabelParseError = BabelElabError {
    import preExpr._

    val Location( begin, endAfterWS ) = err.loc.getOrElse( Location( 0, text.size ) )
    val end = text.lastIndexWhere( !_.isWhitespace, endAfterWS - 1 ) + 1
    val snippet =
      text.view.zipWithIndex.
        map {
          case ( '\n', _ )                            => '\n'
          case ( _, i ) if i == begin && i == end - 1 => '╨'
          case ( _, i ) if i == begin                 => '╘'
          case ( _, i ) if i == end - 1               => '╛'
          case ( _, i ) if begin < i && i < end       => '═'
          case ( _, _ )                               => ' '
        }.mkString.lines.zip( text.lines ).
        map {
          case ( markers, code ) if markers.trim.nonEmpty => s"  $code\n  $markers\n"
          case ( _, code )                                => s"  $code\n"
        }.mkString.stripLineEnd

    val readable = new preExpr.ReadablePrinter( err.assg, sig )

    s"""
       |${err.msg}
       |
       |$snippet
       |${err.expected.map( e => s"\nexpected type: ${readable( e )}\n" ).getOrElse( "" )}
       |actual type: ${readable( err.actual )}
     """.stripMargin
  }

  /**
   * Parses text as a lambda expression, or returns a parse error.
   *
   * @param astTransformer  Function to apply to the Babel AST before type inference.
   * @param sig  Babel signature that specifies which free variables are constants.
   */
  def tryParse( text: String, astTransformer: preExpr.Expr => preExpr.Expr = identity )( implicit sig: BabelSignature ): Either[BabelParseError, Expr] = {
    ExprAndNothingElse.parse( text ) match {
      case Parsed.Success( expr, _ ) =>
        val transformedExpr = astTransformer( expr )
        preExpr.toRealExpr( transformedExpr, sig ).leftMap( ppElabError( text, _ ) )
      case parseError @ Parsed.Failure( _, _, _ ) =>
        Left( BabelParsingError( parseError ) )
    }
  }

  /** Parses text as a lambda expression, or throws an exception. */
  def parse( text: String )( implicit sig: BabelSignature ): Expr =
    tryParse( text ).fold( throw _, identity )
  /** Parses text as a formula, or throws an exception. */
  def parseFormula( text: String )( implicit sig: BabelSignature ): Formula =
    tryParse( text, preExpr.TypeAnnotation( _, preExpr.Bool ) ).fold( throw _, _.asInstanceOf[Formula] )

  def tryParseType( text: String ): Either[BabelParseError, real.Ty] = {
    TypeAndNothingElse.parse( text ) match {
      case Parsed.Success( expr, _ ) =>
        Right( preExpr.toRealType( expr, Map() ) )
      case parseError @ Parsed.Failure( _, _, _ ) =>
        Left( BabelParsingError( parseError ) )
    }
  }

  def tryParseSequent( text: String, astTransformer: preExpr.Expr => preExpr.Expr = identity )( implicit sig: BabelSignature ): Either[BabelParseError, Sequent[Expr]] = {
    SequentAndNothingElse.parse( text ) match {
      case Parsed.Success( exprSequent, _ ) =>
        val transformed = exprSequent.map( astTransformer )
        preExpr.toRealExprs( transformed.elements, sig ).leftMap( ppElabError( text, _ ) ).map { sequentElements =>
          val ( ant, suc ) = sequentElements.
            splitAt( exprSequent.antecedent.size )
          HOLSequent( ant, suc )
        }
      case parseError @ Parsed.Failure( _, _, _ ) =>
        Left( BabelParsingError( parseError ) )
    }
  }

  def tryParseLabelledSequent( text: String, astTransformer: preExpr.Expr => preExpr.Expr = identity )( implicit sig: BabelSignature ): Either[BabelParseError, Sequent[( String, Formula )]] = {
    LabelledSequentAndNothingElse.parse( text ) match {
      case Parsed.Success( exprSequent, _ ) =>
        val transformed = for ( ( l, f ) <- exprSequent ) yield l -> preExpr.TypeAnnotation( astTransformer( f ), preExpr.Bool )
        preExpr.toRealExprs( transformed.elements.map( _._2 ), sig ).leftMap( ppElabError( text, _ ) ).map { sequentElements =>
          val ( ant, suc ) = exprSequent.map( _._1 ).elements.
            zip( sequentElements.map( _.asInstanceOf[Formula] ) ).
            splitAt( exprSequent.antecedent.size )
          val nameGen = new NameGenerator( exprSequent.elements.view.flatMap( _._1 ).toSet )
          HOLSequent( ant, suc ).zipWithIndex.map {
            case ( ( Some( l ), f ), _ ) => l -> f
            case ( ( None, f ), i )      => guessLabels.suggestLabel( f, i, nameGen ) -> f
          }
        }
      case parseError @ Parsed.Failure( _, _, _ ) =>
        Left( BabelParsingError( parseError ) )
    }
  }
}
