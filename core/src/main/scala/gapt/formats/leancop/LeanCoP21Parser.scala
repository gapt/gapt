package gapt.formats.leancop

import gapt.expr.formula.{ Atom, Eq }
import gapt.expr.formula.fol.{ FOLAtom, FOLFunction, FOLTerm }
import gapt.proofs.FOLClause

object LeanCoP21Parser {
  sealed trait Lit
  case class Pos( atom: FOLAtom ) extends Lit
  case class Neg( atom: FOLAtom ) extends Lit
  case object Hash extends Lit
  case object NegHash extends Lit

  case class Clause( literals: Lit* ) {
    override def toString = s"Clause(${literals.mkString( ", " )})"

    def toFOLClause: FOLClause =
      FOLClause(
        literals.collect { case Neg( a ) => a },
        literals.collect { case Pos( a ) => a } )
  }

  case class Proof( main: Clause, sides: List[Proof] ) {
    def clauses: List[Clause] =
      main :: sides.flatMap( _.clauses )

    def toFOLClauses: Seq[FOLClause] =
      clauses.map( _.toFOLClause )
  }

  import fastparse._, MultiLineWhitespace._

  def stdout[_: P]: P[Proof] =
    P( ( AnyChar ~ !"ompact Proof" ).rep ~
      "Compact Proof:\n--------------" ~ proof ~ "--------------" )

  def proof[_: P]: P[Proof] =
    P( "[" ~ clause ~ ( "," ~/ proof ).rep ~ "]" ).map {
      case ( main, sides ) => Proof( main, sides.toList )
    }

  def clause[_: P]: P[Clause] =
    P( "[" ~ lit.rep( sep = "," ) ~ "]" ).map( Clause( _: _* ) )

  def lit[_: P]: P[Lit] = P( pos | neg | hash | negHash )
  def pos[_: P]: P[Lit] = P( atom ).map( Pos )
  def neg[_: P]: P[Lit] = P( "-" ~ atom ).map( Neg )
  def hash[_: P]: P[Lit] = P( "#" ).map( _ => Hash )
  def negHash[_: P]: P[Lit] = P( "-" ~ "#" ).map( _ => NegHash )

  def atom[_: P]: P[FOLAtom] = P( ( ident ~ ( "(" ~ term.rep( sep = "," ) ~ ")" ).? ~ ( "=" ~ term ).? )
    .map {
      case ( n, as, None )        => FOLAtom( n, as.getOrElse( Nil ) )
      case ( n, as, Some( rhs ) ) => Eq( FOLFunction( n, as.getOrElse( Nil ) ), rhs )
    } | ( "(" ~ atom ~ ")" ) )

  def term[_: P]: P[FOLTerm] = P( ident ~ ( "(" ~ term.rep( sep = "," ) ~ ")" ).? )
    .map { case ( n, as ) => FOLFunction( n, as.getOrElse( Nil ) ) }

  def ident[_: P]: P[String] = P( CharsWhile( c => c.isLetterOrDigit || c == '_', 1 ).! )

  def parse( stdout: String ): Either[String, Proof] =
    fastparse.parse( stdout, LeanCoP21Parser.stdout( _ ) ) match {
      case Parsed.Success( prf, _ ) => Right( prf )
      case fail: Parsed.Failure     => Left( fail.msg )
    }

}