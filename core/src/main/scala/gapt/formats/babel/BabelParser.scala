package gapt.formats.babel

import gapt.{ expr => real }
import gapt.expr.{ Formula, Expr, preExpr }
import gapt.proofs.gaptic.guessLabels
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.utils.NameGenerator
import cats.syntax.either._

object Precedence {
  val min = 0

  val ident = 30
  val app = 28
  val timesDiv = 26
  val plusMinus = 24
  val infixRel = 22
  val neg = 20
  val quant = 20
  val conj = 18
  val disj = 14
  val iff = 12
  val impl = 10
  val typeAnnot = 8
  val lam = 6

  val max = Integer.MAX_VALUE
}

sealed abstract class BabelParseError( message: String ) extends IllegalArgumentException( message )
case class BabelElabError( reason: String ) extends BabelParseError( reason )
case class BabelParsingError( parseError: fastparse.Parsed.Failure )
  extends BabelParseError( parseError.trace.longAggregateMsg )

object BabelLexical {
  import fastparse._, NoWhitespace._

  def isOpChar( c: Char ) =
    c != 'λ' && c != '⊢' && c != ',' && c != '(' && c != ')' && c != '\'' && c != '#' && c != ':' &&
      c != '\\' && c != '^' &&
      !isUnquotNameChar( c ) && {
        val ty = c.getType
        ty != Character.SPACE_SEPARATOR && (
          ty == Character.MATH_SYMBOL || ty == Character.OTHER_SYMBOL || ( '\u0020' <= c && c <= '\u007e' ) )
      }
  def OpChar[_: P] = CharPred( isOpChar )
  def RestOpChar[_: P] = OpChar | CharIn( "_" ) | CharPred( isUnquotNameChar )
  def Operator[_: P]: P[String] = P( ( OpChar.rep( 1 ) ~ ( "_" ~ RestOpChar.rep ).? ).! )
  def OperatorAndNothingElse[_: P] = Operator ~ End

  def Name[_: P]: P[String] = P( Operator | UnquotedName | QuotedName )
  def TyName[_: P]: P[String] = P( UnquotedName | QuotedName )
  def isEmoji( c: Char ) = ( '\ud83c' <= c && c <= '\udbff' ) || ( '\udc00' <= c && c <= '\udfff' )
  def isUnquotNameChar( c: Char ) = ( c.isUnicodeIdentifierPart || isEmoji( c ) || c == '_' || c == '$' ) && c != 'λ'
  def UnquotedName[_: P]: P[String] = P( CharsWhile( isUnquotNameChar ).! )
  def QuotedName[_: P]: P[String] = P( "'" ~ QuotedNameChar.rep ~ "'" ).map( _.mkString )
  def QuotedNameChar[_: P]: P[String] = P(
    CharsWhile( c => c != '\\' && c != '\'' ).! |
      ( "\\" ~ ( "'" | "\\" ).! ) |
      ( "\\u" ~ CharIn( "0123456789abcdef" ).
        rep( min = 4, max = 4 ).!.
        map( Integer.parseInt( _, 16 ).toChar.toString ) ) )

  def kw[_: P]( name: String ) = P( name ~ !CharPred( isUnquotNameChar ) )
}

object BabelParserCombinators {
  import BabelLexical._
  import fastparse._, MultiLineWhitespace._

  def MarkPos[_: P]( p: => P[preExpr.Expr] ): P[preExpr.Expr] = {
    val begin = P.current.index
    val result = p
    val end = P.current.index
    result.map {
      case annotated @ preExpr.LocAnnotation( _, _ ) =>
        annotated
      case unannotated =>
        preExpr.LocAnnotation( unannotated, preExpr.Location( begin, end ) )
    }
  }

  def ExprAndNothingElse[_: P]: P[preExpr.Expr] = P( "" ~ Expr ~ End )

  def Expr[_: P]: P[preExpr.Expr] = P( Lam )

  def BoundVar[_: P]: P[preExpr.Ident] = P(
    Name.map( preExpr.Ident( _, preExpr.freshMetaType(), None ) ) |
      ( "(" ~ Name ~ ":" ~ Type ~ ")" ).map( x => preExpr.Ident( x._1, x._2, None ) ) )
  def Lam[_: P]: P[preExpr.Expr] = MarkPos( P( ( ( "^" | "λ" ) ~/ BoundVar ~ Lam ).
    map( x => preExpr.Abs( x._1, x._2 ) ) | TypeAnnotation ) )

  def TypeAnnotation[_: P]: P[preExpr.Expr] = MarkPos( P( ( FlatOps ~/ ( ":" ~ Type ).? ) map {
    case ( expr, Some( ty ) ) => preExpr.TypeAnnotation( expr, ty )
    case ( expr, None )       => expr
  } ) )

  def FlatOps[_: P]: P[preExpr.Expr] = MarkPos( P( FlatOpsElem.rep( 1 ).map( children => preExpr.FlatOps( children.view.flatten.toList ) ) ) )
  def FlatOpsElem[_: P]: P[Seq[preExpr.FlatOpsChild]] = P(
    ( Ident.map { case preExpr.LocAnnotation( preExpr.Ident( n, _, None ), loc ) => Left( ( n, loc ) ) case e => Right( e ) } |
      ( VarLiteral | ConstLiteral ).map( Right( _ ) ) ).map( Seq( _ ) )
      | Tuple.map( _.map( Right( _ ) ) ) )

  def Fn[_: P]: P[preExpr.Expr] = MarkPos( P( Ident | VarLiteral | ConstLiteral ) )
  def Tuple[_: P]: P[Seq[preExpr.Expr]] = P( "(" ~/ Expr.rep( sep = "," ) ~ ")" )

  def Parens[_: P] = MarkPos( P( "(" ~/ Expr ~/ ")" ) )

  def Var[_: P] = P( Name ~ ":" ~ Type ) map {
    case ( name, ty ) => real.Var( name, preExpr.toRealType( ty, Map() ) )
  }
  def TyParams[_: P] = P( "{" ~ Type.rep ~ "}" )
  def Const[_: P] = P( Name ~ TyParams.? ~ ":" ~ Type ) map {
    case ( name, ps, ty ) => real.Const( name, preExpr.toRealType( ty, Map() ),
      ps.getOrElse( Nil ).toList.map( preExpr.toRealType( _, Map() ) ) )
  }
  def VarLiteral[_: P] = MarkPos( P( ( "#v(" ~/ Var ~ ")" ).map { preExpr.QuoteBlackbox } ) )
  def ConstLiteral[_: P] = MarkPos( P( ( "#c(" ~/ Const ~ ")" ).map { preExpr.QuoteBlackbox } ) )

  def Ident[_: P]: P[preExpr.Expr] = MarkPos( P( ( Name ~ TyParams.? ).map {
    case ( n, ps ) =>
      preExpr.Ident( n, preExpr.freshMetaType(), ps.map( _.toList ) )
  } ) )

  def TypeParens[_: P]: P[preExpr.Type] = P( "(" ~/ Type ~ ")" )
  def TypeBase[_: P]: P[preExpr.Type] = P( TyName ~ TypeAtom.rep ).map { case ( n, ps ) => preExpr.BaseType( n, ps.toList ) }
  def TypeVar[_: P]: P[preExpr.Type] = P( "?" ~/ TyName ).map( preExpr.VarType )
  def TypeAtom[_: P]: P[preExpr.Type] = P( TypeParens | TypeVar | TypeBase )
  def Type[_: P]: P[preExpr.Type] = P( TypeAtom.rep( min = 1, sep = ">" ) ).map { _.reduceRight( preExpr.ArrType ) }
  def TypeAndNothingElse[_: P] = P( "" ~ Type ~ End )

  def Sequent[_: P] = P( Expr.rep( sep = "," ) ~ ( ":-" | "⊢" ) ~ Expr.rep( sep = "," ) ).
    map { case ( ant, suc ) => HOLSequent( ant, suc ) }
  def SequentAndNothingElse[_: P] = P( "" ~ Sequent ~ End )

  def LabelledFormula[_: P] = P( ( TyName ~ ":" ~ !"-" ).? ~ Expr )
  def LabelledSequent[_: P] = P( LabelledFormula.rep( sep = "," ) ~ ( ":-" | "⊢" ) ~ LabelledFormula.rep( sep = "," ) ).
    map { case ( ant, suc ) => HOLSequent( ant, suc ) }
  def LabelledSequentAndNothingElse[_: P] = P( "" ~ LabelledSequent ~ End )
}

object BabelParser {
  import BabelParserCombinators._
  import fastparse._

  private def ppElabError( text: String, err: preExpr.ElabError )(
    implicit
    sig: BabelSignature ): BabelParseError = BabelElabError {
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
        }.mkString.linesIterator.zip( text.linesIterator ).
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
       |${err.actual.map( a => s"actual type: ${readable( a )}" ).getOrElse( "" )}
     """.stripMargin
  }

  /**
   * Parses text as a lambda expression, or returns a parse error.
   *
   * @param astTransformer  Function to apply to the Babel AST before type inference.
   * @param sig  Babel signature that specifies which free variables are constants.
   */
  def tryParse(
    text:           String,
    astTransformer: preExpr.Expr => preExpr.Expr = identity )( implicit sig: BabelSignature ): Either[BabelParseError, Expr] = {
    fastparse.parse( text, ExprAndNothingElse( _ ) ) match {
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
    fastparse.parse( text, TypeAndNothingElse( _ ) ) match {
      case Parsed.Success( expr, _ ) =>
        Right( preExpr.toRealType( expr, Map() ) )
      case parseError @ Parsed.Failure( _, _, _ ) =>
        Left( BabelParsingError( parseError ) )
    }
  }

  def tryParseSequent(
    text:           String,
    astTransformer: preExpr.Expr => preExpr.Expr = identity )(
    implicit
    sig: BabelSignature ): Either[BabelParseError, Sequent[Expr]] = {
    fastparse.parse( text, SequentAndNothingElse( _ ) ) match {
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

  def tryParseLabelledSequent(
    text:           String,
    astTransformer: preExpr.Expr => preExpr.Expr = identity )(
    implicit
    sig: BabelSignature ): Either[BabelParseError, Sequent[( String, Formula )]] = {
    fastparse.parse( text, LabelledSequentAndNothingElse( _ ) ) match {
      case Parsed.Success( exprSequent, _ ) =>
        val transformed = for ( ( l, f ) <- exprSequent )
          yield l -> preExpr.TypeAnnotation( astTransformer( f ), preExpr.Bool )
        preExpr.toRealExprs( transformed.elements.map( _._2 ), sig )
          .leftMap( ppElabError( text, _ ) ).map { sequentElements =>
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
