package at.logic.gapt.formats.babel

import at.logic.gapt.expr.{ HOLFormula, LambdaExpression }

import scalaz._
import Scalaz._

object BabelLexical {
  import fastparse.all._

  val Whitespace = NoTrace( CharsWhile( _.isWhitespace, min = 0 ) )

  val Name: P[String] = P( UnquotedName | QuotedName )
  val UnquotedName: P[String] = P( CharsWhile( c => c.isLetterOrDigit || c == '_' || c == '$' ).! )
  val QuotedName: P[String] = P( "'" ~ QuotedNameChar.rep ~ "'" ).map( _.mkString )
  val QuotedNameChar: P[String] = P(
    CharsWhile( c => c != '\\' && c != ''' ).! |
      ( "\\" ~ ( "'" | "\\" ).! ) |
      ( "\\u" ~ CharIn( ( 'a' to 'f' ) ++ ( '0' to '9' ) ).
        rep( min = 4, max = 4 ).!.
        map( Integer.parseInt( _, 16 ).toChar.toString ) )
  )
}

object BabelParser {
  import BabelLexical._
  import fastparse.noApi._
  val White = fastparse.WhitespaceApi.Wrapper( Whitespace )
  import White._

  val ExprAndNothingElse: P[ast.Expr] = P( "" ~ Expr ~ End )

  val Expr: P[ast.Expr] = P( Lam )

  val BoundVar: P[ast.Ident] = P( Ident | ( "(" ~ Name ~ ":" ~ Type ~ ")" ).map( x => ast.Ident( x._1, x._2 ) ) )
  val Lam: P[ast.Expr] = P( ( ( "^" | "\\" | "λ" ) ~/ BoundVar ~ "=>".? ~ Lam ).map( x => ast.Abs( x._1, x._2 ) ) | TypeAscription )

  val TypeAscription: P[ast.Expr] = P( Impl ~/ ( ":" ~ Type ).? ) map {
    case ( expr, Some( ty ) ) => ast.TypeAscription( expr, ty )
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
  val Ex = P( ( "?" | "∃" | "exists" ) ~/ BoundVar ~ QuantOrNeg ).map( ast.Ex.tupled )
  val All = P( ( "!" | "∀" | "all" ) ~/ BoundVar ~ QuantOrNeg ).map( ast.All.tupled )
  val Neg: P[ast.Expr] = P( ( "-" | "¬" ) ~ QuantOrNeg ).map( ast.Neg )

  val InfixRelSym = P( "<" | ">" | "<=" | ">=" | "=" | "!=" )
  val InfixRel = P( PlusMinus ~/ ( InfixRelSym.! ~ PlusMinus ).rep ) map {
    case ( first, Seq() ) => first
    case ( first, conds ) =>
      val terms = first +: conds.map { _._2 }
      val rels = conds.map { _._1 }
      ( terms, rels, terms.tail ).zipped.map {
        case ( a, "!=", b ) => ast.Neg( ast.Eq( a, b ) )
        case ( a, "=", b )  => ast.Eq( a, b )
        case ( a, r, b ) =>
          ast.TypeAscription( ast.App( ast.App( ast.Ident( r, ast.freshTypeVar() ), a ), b ), ast.Bool )
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
  val App: P[ast.Expr] = P( "@".? ~ Atom ~/ ( Tuple | Ident.map( Seq( _ ) ) ).rep ) map {
    case ( expr, args ) => args.flatten.foldLeft( expr )( ast.App )
  }

  val Parens: P[ast.Expr] = P( "(" ~/ Expr ~/ ")" )
  val Atom: P[ast.Expr] = P( Parens | Ident )

  val Ident: P[ast.Ident] = P( Name.map( ast.Ident( _, ast.freshTypeVar() ) ) )

  val TypeParens: P[ast.Type] = P( "(" ~ Type ~ ")" )
  val TypeBase: P[ast.Type] = P( Name ).map( ast.BaseType )
  val Type: P[ast.Type] = P( ( TypeParens | TypeBase ).rep( min = 1, sep = ">" ) ).map { _.reduceRight( ast.ArrType ) }

  def parse( text: String ): String \/ LambdaExpression = {
    ExprAndNothingElse.parse( text ) match {
      case Parsed.Success( expr, _ ) =>
        ast.toRealExpr( expr ).leftMap { unifError =>
          s"Cannot type-check ${ast.readable( expr )}:\n$unifError"
        }
      case parseError: Parsed.Failure =>
        parseError.toString.left
    }
  }

  def parseFormula( text: String ): String \/ HOLFormula = {
    ExprAndNothingElse.parse( text ) match {
      case Parsed.Success( expr, _ ) =>
        val formula = ast.TypeAscription( expr, ast.Bool )
        ast.toRealExpr( formula ).leftMap { unifError =>
          s"Cannot type-check ${ast.readable( formula )}:\n$unifError"
        }.map { _.asInstanceOf[HOLFormula] }
      case parseError: Parsed.Failure =>
        parseError.toString.left
    }
  }
}
