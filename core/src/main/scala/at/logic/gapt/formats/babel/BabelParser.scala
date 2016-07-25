package at.logic.gapt.formats.babel

import at.logic.gapt.{ expr => real }
import at.logic.gapt.expr.{ HOLFormula, LambdaExpression }
import at.logic.gapt.proofs.{ Sequent, HOLSequent }

import scalaz._
import Scalaz._

sealed abstract class BabelParseError( message: String ) extends IllegalArgumentException( message )
case class BabelUnificationError( reason: String ) extends BabelParseError( reason )
case class BabelParsingError( parseError: fastparse.core.ParseError ) extends BabelParseError( parseError.getMessage )

object BabelLexical {
  import fastparse.all._

  val Whitespace = NoTrace( CharsWhile( _.isWhitespace, min = 0 ) )

  val Name: P[String] = P( UnquotedName | QuotedName )
  def isUnquotNameChar( c: Char ) = ( c.isLetterOrDigit || c == '_' || c == '$' ) && c != 'λ'
  val UnquotedName: P[String] = P( CharsWhile( isUnquotNameChar ).! )
  val QuotedName: P[String] = P( "'" ~ QuotedNameChar.rep ~ "'" ).map( _.mkString )
  val QuotedNameChar: P[String] = P(
    CharsWhile( c => c != '\\' && c != ''' ).! |
      ( "\\" ~ ( "'" | "\\" ).! ) |
      ( "\\u" ~ CharIn( ( 'a' to 'f' ) ++ ( '0' to '9' ) ).
        rep( min = 4, max = 4 ).!.
        map( Integer.parseInt( _, 16 ).toChar.toString ) )
  )

  val keywords = Set( "true", "false", "all", "exists" )

  def kw( name: String ) = P( name ~ !CharPred( isUnquotNameChar ) )
}

object BabelParserCombinators {
  import BabelLexical._
  import fastparse.noApi._
  val White = fastparse.WhitespaceApi.Wrapper( Whitespace )
  import White._

  val ExprAndNothingElse: P[ast.Expr] = P( "" ~ Expr ~ End )
  val ConstAndNothingElse: P[real.Const] = P( "" ~ Const ~ End )

  val Expr: P[ast.Expr] = P( Lam )

  val BoundVar: P[ast.Ident] = P( Ident | ( "(" ~ Name ~ ":" ~ Type ~ ")" ).map( x => ast.Ident( x._1, x._2 ) ) )
  val Lam: P[ast.Expr] = P( ( ( "^" | "\\" | "λ" ) ~/ BoundVar ~ "=>".? ~ Lam ).map( x => ast.Abs( x._1, x._2 ) ) | TypeAnnotation )

  val TypeAnnotation: P[ast.Expr] = P( Impl ~/ ( ":" ~ Type ).? ) map {
    case ( expr, Some( ty ) ) => ast.TypeAnnotation( expr, ty )
    case ( expr, None )       => expr
  }

  val Impl: P[ast.Expr] = P( Bicond.rep( 1, "->" | "⊃" ) ).map( _.reduceRight( ast.Imp ) )
  val Bicond: P[ast.Expr] = P( Disj.rep( 1, "<->" ) ).map {
    case Seq( formula ) => formula
    case formulas       => ( formulas, formulas.tail ).zipped.map( ast.Bicond ).reduceLeft( ast.And )
  }

  val Disj = P( Conj.rep( 1, "|" | "∨" ) ).map( _.reduceLeft( ast.Or ) )

  val Conj = P( QuantOrNeg.rep( 1, "&" | "∧" ) ).map( _.reduceLeft( ast.And ) )

  val QuantOrNeg: P[ast.Expr] = P( Ex | All | Neg | InfixRel )
  val Ex = P( ( "?" | "∃" | kw( "exists" ) ) ~/ BoundVar ~ QuantOrNeg ).map( ast.Ex.tupled )
  val All = P( ( "!" | "∀" | kw( "all" ) ) ~/ BoundVar ~ QuantOrNeg ).map( ast.All.tupled )
  val Neg: P[ast.Expr] = P( ( "-" | "¬" ) ~ QuantOrNeg ).map( ast.Neg )

  val InfixRelSym = P( "<=" | ">=" | "<" | ">" | "=" | "!=" )
  val InfixRel = P( PlusMinus ~/ ( InfixRelSym.! ~ PlusMinus ).rep ) map {
    case ( first, Seq() ) => first
    case ( first, conds ) =>
      val terms = first +: conds.map { _._2 }
      val rels = conds.map { _._1 }
      ( terms, rels, terms.tail ).zipped.map {
        case ( a, "!=", b ) => ast.Neg( ast.Eq( a, b ) )
        case ( a, "=", b )  => ast.Eq( a, b )
        case ( a, r, b ) =>
          ast.TypeAnnotation( ast.App( ast.App( ast.Ident( r, ast.freshTypeVar() ), a ), b ), ast.Bool )
      }.reduceLeft( ast.And )
  }

  val PlusMinus: P[ast.Expr] = P( TimesDiv ~/ ( ( "+" | "-" ).! ~ TimesDiv ).rep ) map {
    case ( first, rest ) =>
      rest.foldLeft( first ) { case ( a, ( o, b ) ) => ast.App( ast.App( ast.Ident( o, ast.freshTypeVar() ), a ), b ) }
  }

  val TimesDiv: P[ast.Expr] = P( App ~/ ( ( "*" | "/" ).! ~ App ).rep ) map {
    case ( first, rest ) =>
      rest.foldLeft( first ) { case ( a, ( o, b ) ) => ast.App( ast.App( ast.Ident( o, ast.freshTypeVar() ), a ), b ) }
  }

  val Tuple: P[Seq[ast.Expr]] = P( "(" ~/ Expr.rep( sep = "," ) ~ ")" )
  val App: P[ast.Expr] = P( "@".? ~ Atom ~/ ( Tuple | Atom.map( Seq( _ ) ) ).rep ) map {
    case ( expr, args ) => args.flatten.foldLeft( expr )( ast.App )
  }

  val Parens: P[ast.Expr] = P( "(" ~/ Expr ~/ ")" )
  val Atom: P[ast.Expr] = P( Parens | True | False | VarLiteral | ConstLiteral | Ident )

  val True = P( kw( "true" ) | "⊤" ).map( _ => ast.Top )
  val False = P( kw( "false" ) | "⊥" ).map( _ => ast.Bottom )

  val Var = P( Name ~ ":" ~ Type ) map {
    case ( name, ty ) => real.Var( name, ast.toRealType( ty, Map() ) )
  }
  val Const = P( Name ~ ":" ~ Type ) map {
    case ( name, ty ) => real.Const( name, ast.toRealType( ty, Map() ) )
  }
  val VarLiteral = P( "#v(" ~/ Var ~ ")" ) map { ast.LiftBlackbox }
  val ConstLiteral = P( "#c(" ~/ Const ~ ")" ) map { ast.LiftBlackbox }

  val Ident: P[ast.Ident] = P( Name.map( ast.Ident( _, ast.freshTypeVar() ) ) )

  val TypeParens: P[ast.Type] = P( "(" ~/ Type ~ ")" )
  val TypeBase: P[ast.Type] = P( Name ).map( ast.BaseType )
  val Type: P[ast.Type] = P( ( TypeParens | TypeBase ).rep( min = 1, sep = ">" ) ).map { _.reduceRight( ast.ArrType ) }

  val Sequent = P( Expr.rep( sep = "," ) ~ ( ":-" | "⊢" ) ~ Expr.rep( sep = "," ) ).
    map { case ( ant, suc ) => HOLSequent( ant, suc ) }
  val SequentAndNothingElse = P( "" ~ Sequent ~ End )
}

object BabelParser {
  import BabelParserCombinators._
  import fastparse.noApi._

  /**
   * Parses text as a lambda expression, or returns a parse error.
   *
   * @param astTransformer  Function to apply to the Babel AST before type inference.
   * @param sig  Babel signature that specifies which free variables are constants.
   */
  def tryParse( text: String, astTransformer: ast.Expr => ast.Expr = identity )( implicit sig: BabelSignature ): BabelParseError \/ LambdaExpression = {
    import fastparse.core.Parsed._
    ExprAndNothingElse.parse( text ) match {
      case Success( expr, _ ) =>
        val transformedExpr = astTransformer( expr )
        ast.toRealExpr( transformedExpr, sig ).leftMap { unifError =>
          BabelUnificationError( s"Cannot type-check ${ast.readable( transformedExpr )}:\n$unifError" )
        }
      case parseError: Failure =>
        BabelParsingError( ParseError( parseError ) ).left
    }
  }

  /** Parses text as a lambda expression, or throws an exception. */
  def parse( text: String )( implicit sig: BabelSignature ): LambdaExpression =
    tryParse( text ).fold( throw _, identity )
  /** Parses text as a formula, or throws an exception. */
  def parseFormula( text: String )( implicit sig: BabelSignature ): HOLFormula =
    tryParse( text, ast.TypeAnnotation( _, ast.Bool ) ).fold( throw _, _.asInstanceOf[HOLFormula] )

  def tryParseSequent( text: String, astTransformer: ast.Expr => ast.Expr = identity )( implicit sig: BabelSignature ): BabelParseError \/ Sequent[LambdaExpression] = {
    import fastparse.core.Parsed._
    SequentAndNothingElse.parse( text ) match {
      case Success( exprSequent, _ ) =>
        val transformed = exprSequent.map( astTransformer )
        ast.toRealExprs( transformed.elements, sig ).leftMap { unifError =>
          BabelUnificationError( s"Cannot type-check ${transformed.map( ast.readable )}:\n$unifError" )
        }.map { sequentElements =>
          val ( ant, suc ) = sequentElements.
            splitAt( exprSequent.antecedent.size )
          HOLSequent( ant, suc )
        }
      case parseError: Failure =>
        BabelParsingError( ParseError( parseError ) ).left
    }
  }
}
