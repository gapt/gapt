package gapt.formats.leancop

import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Iff
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.subst.FOLSubstitution
import gapt.formats.InputFile
import gapt.logic.Polarity
import gapt.proofs.FOLClause
import gapt.proofs.Sequent
import gapt.proofs.expansion.ExpansionSequent
import gapt.provers.leancop.leanCoPProofToExpansionSequent

import java.io.Reader
import java.io.StringReader
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.RegexParsers

class LeanCoPParserException( msg: String ) extends Exception( msg: String )
class LeanCoPNoMatchException( msg: String ) extends Exception( msg: String )
class LeanCoPNoLeanPredException( msg: String ) extends Exception( msg: String )
class LeanCoPLeanPredWrongArityException( msg: String ) extends Exception( msg: String )

object LeanCoPParser extends RegexParsers with PackratParsers {

  override def skipWhitespace: Boolean = true

  private val nLine = sys.props( "line.separator" )

  def parseAsExpansionSequent( file: InputFile ): ExpansionSequent =
    leanCoPProofToExpansionSequent( parseLeanProof( file ) )

  def parseLeanProof( file: InputFile ): LeanProof = {
    parseLeanProof( new StringReader( file.read ) )
  }

  def parseLeanProof( reader: Reader ): LeanProof = {
    parseAll( leanProof, reader ) match {
      case Success( r, _ ) => r
      case Failure( msg, next ) =>
        throw new LeanCoPParserException(
          "leanCoP parsing: syntax failure " + msg + nLine +
            "at line " + next.pos.line + " and column " + next.pos.column )
      case Error( msg, next ) =>
        throw new LeanCoPParserException( "leanCoP parsing: syntax error " + msg + nLine +
          "at line " + next.pos.line + " and column " + next.pos.column )
    }
  }

  object FOLLiteral {
    def unapply( f: FOLFormula ): Option[( Polarity, FOLAtom )] =
      f match {
        case a @ FOLAtom( _, _ )        => Some( Polarity.Positive, a )
        case Neg( a @ FOLAtom( _, _ ) ) => Some( Polarity.Negative, a )
        case _                          => None
      }
  }

  type LeanPredicate = ( String, Int )
  type Name = String
  type Role = String
  type ClauseIndex = Int

  case class LeanProof(
      initialFormulas: Seq[InputFormula],
      clauses:         Seq[LeanCoPClause],
      instances:       Seq[LeanInstance] )
  case class InputFormula( name: Name, role: Role, formula: FOLFormula )
  case class LeanCoPClause( index: ClauseIndex, cls: FOLClause, origin: Name )
  case class LeanInstance( index: ClauseIndex, substitution: FOLSubstitution )

  // todo: LeanCoP does not do a VNF so reading back as we currently do is
  //       dangerous. We should do a VNF on the formulas before passing it to lean.

  // todo: This interface probably only works in a situation where we have control over
  //       the provers input, because it allows us to reconstruct the proof.
  //       Without having control over the clausification, reading back a proof is painful, because we do not know
  //       where a given leanCoP clause comes from.

  // todo: make this introduce false___ and true___

  def leanProof: Parser[LeanProof] =
    rep( comment ) ~>
      rep( input ) ~ rep( comment ) ~ rep( clauses ) ~ rep( comment ) ~ rep( inferences ) <~
      rep( comment ) ^^ {
        case input ~ _ ~ clauses_lst ~ _ ~ bindings_opt =>
          val inputs = input.map { case ( n, r, f ) => InputFormula( n, r, f ) }
          val clauses = clauses_lst.map { case ( i, f, n ) => LeanCoPClause( i, f, n ) }
          val instances = bindings_opt.flatten.map {
            case ( i, vs, ts ) =>
              LeanInstance( i, FOLSubstitution( vs.zip( ts ) ) )
          }
          LeanProof( inputs, clauses, instances )
      }

  def input: Parser[( String, String, FOLFormula )] =
    language ~ "(" ~>
      name ~ "," ~ role ~ "," ~ formula <~
      "," ~ "file" ~ "(" ~ "[^()]*".r ~ ")" ~ ")" ~ "." ^^ {
        case n ~ _ ~ r ~ _ ~ f => ( n, r, f )
      }

  def clauses: Parser[( Int, FOLClause, String )] =
    language ~ "(" ~>
      integer ~ "," ~ "plain" ~ "," ~ clause ~ "," ~ "clausify" ~ "(" ~ name <~
      ")" ~ ")" ~ "." ^^ {
        case i ~ _ ~ _ ~ _ ~ f ~ _ ~ _ ~ _ ~ n =>
          assert( n != "lean_eq_theory" )
          ( i, f, n )
      } | language ~ "(" ~>
      integer ~ "," ~ "plain" ~ "," ~ clause <~
      "," ~ "theory" ~ "(" ~ "equality" ~ ")" ~ ")" ~ "." ^^ {
        // Equality theory added by leanCoP
        case i ~ _ ~ _ ~ _ ~ f => ( i, f, "lean_eq_theory" )
      }

  def inferences: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] =
    language ~ "(" ~ name ~ "," ~ "plain" ~ "," ~ clause ~ "," ~> info <~ ")" ~ "." ^^ {
      case bindings => bindings
    }

  def language: Parser[String] = "fof" | "cnf"

  def role: Parser[String] = "axiom" | "conjecture" | "lemma" | "hypothesis"

  def info: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] =
    start | start_bind | reduction | extension | ext_w_bind

  def start: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] =
    "start(" ~> integer <~ ")" ^^ { case _ => None }

  def start_bind: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] =
    "start(" ~> integer ~ "," ~ "bind" ~ "(" ~ list_subs <~ ")" ~ ")" ^^ {
      case n ~ _ ~ _ ~ _ ~ ls => Some( ( n, ls._1, ls._2 ) )
    }
  def reduction: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] =
    "reduction" ~ "(" ~ "'" ~> integer <~ "'" ~ ")" ^^ { case _ => None }

  def extension: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] =
    "extension" ~ "(" ~> integer <~ ")" ^^ { case _ => None }

  def ext_w_bind: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] =
    "extension" ~ "(" ~> integer ~ "," ~ "bind" ~ "(" ~ list_subs <~ ")" ~ ")" ^^ {
      case n ~ _ ~ _ ~ _ ~ ls => Some( ( n, ls._1, ls._2 ) )
    }

  def list_subs: Parser[( List[FOLVar], List[FOLTerm] )] =
    "[" ~ "[" ~> repsep( variable, "," ) ~ "]" ~ "," ~ "[" ~ repsep( term, "," ) <~ "]" ~ "]" ^^ {
      case t ~ _ ~ _ ~ _ ~ v => ( t, v )
    }

  def clause: Parser[FOLClause] =
    "[" ~> repsep( literal, "," ) <~ "]" ^^ { Sequent( _ ) }

  lazy val literal: PackratParser[( FOLAtom, Polarity )] = {
    "(" ~> literal <~ ")" |
      ( "~" | "-" ) ~> clauseAtom ^^ { ( _, Polarity.Negative ) } |
      clauseAtom ^^ { ( _, Polarity.Positive ) } |
      not_eq ^^ { case Neg( a @ FOLAtom( _, _ ) ) => ( a, Polarity.Negative ) }
  }

  lazy val clauseAtom: PackratParser[FOLAtom] =
    atom | "(" ~> atom <~ ")"

  lazy val formula: PackratParser[FOLFormula] = biconditionals

  lazy val biconditionals: PackratParser[FOLFormula] =
    implications ~ "<=>" ~ biconditionals ^^ {
      case f1 ~ _ ~ f2 => Iff( f1, f2 )
    } | implications

  lazy val implications: PackratParser[FOLFormula] =
    disjunctions ~ "=>" ~ implications ^^ {
      case f1 ~ _ ~ f2 => Imp( f1, f2 )
    } | disjunctions

  lazy val disjunctions: PackratParser[FOLFormula] =
    conjunctions ~ rep( "|" ~> conjunctions ) ^^ {
      case f ~ fs => Or( f :: fs )
    }

  lazy val conjunctions: PackratParser[FOLFormula] =
    nonInfixFormula ~ rep( "&" ~> nonInfixFormula ) ^^ {
      case f ~ fs => And( f :: fs )
    }

  lazy val nonInfixFormula: PackratParser[FOLFormula] =
    neg | quantified | formulaInParentheses | not_eq | atom

  lazy val neg: PackratParser[FOLFormula] =
    ( "-" | "~" ) ~> nonInfixFormula ^^ {
      case f => Neg( f )
    }

  lazy val quantified: PackratParser[FOLFormula] =
    "!" ~ "[" ~> repsep( variable, "," ) ~ "]" ~ ":" ~ formula ^^ {
      case vs ~ _ ~ _ ~ f => All.Block( vs, f )
    } | "?" ~ "[" ~> repsep( variable, "," ) ~ "]" ~ ":" ~ formula ^^ {
      case vs ~ _ ~ _ ~ f => Ex.Block( vs, f )
    }

  lazy val formulaInParentheses: PackratParser[FOLFormula] =
    "(" ~> formula <~ ")"

  lazy val not_eq: PackratParser[FOLFormula] = "(" ~ "!" ~> term ~ ")" ~ "=" ~ term ^^ {
    case t1 ~ _ ~ _ ~ t2 => Neg( FOLAtom( "=", List( t1, t2 ) ) )
  }

  lazy val atom: PackratParser[FOLAtom] =
    eq | lean_atom | real_atom

  // These are introduced by leanCoP's (restricted) definitional clausal form translation
  lazy val lean_atom: PackratParser[FOLAtom] = lean_var ^^ {
    case ( i, terms ) =>
      FOLAtom( "leanP" + i, terms )
  }

  lazy val real_atom: PackratParser[FOLAtom] = name ~ opt( "(" ~> repsep( term, "," ) <~ ")" ) ^^ {
    case pred ~ Some( args ) => FOLAtom( pred, args )
    case pred ~ None         => FOLAtom( pred )
  }

  lazy val eq: PackratParser[FOLAtom] = term ~ "=" ~ term ^^ {
    case t1 ~ _ ~ t2 => FOLAtom( "=", List( t1, t2 ) )
  }

  def term: Parser[FOLTerm] =
    skolem_term | variable | function | constant

  def function: Parser[FOLTerm] =
    name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ {
      case f ~ _ ~ args => FOLFunction( f, args )
    }

  def constant: Parser[FOLConst] = name ^^ { case n => FOLConst( n ) }

  def variable: Parser[FOLVar] = """_[A-Z0-9]+""".r ^^ { case n => FOLVar( n ) }

  def skolem_term: Parser[FOLTerm] = lean_var ^^ {
    case ( i, _ ) =>
      // Pretend it's an eigenvariable.
      FOLVar( "leanSk" + i )
  }

  def lean_var: Parser[( Int, List[FOLTerm] )] =
    """\d+""".r ~ "^" ~ "[" ~ repsep( term, "," ) ~ "]" ^^ {
      case i ~ _ ~ _ ~ terms ~ _ => ( i.toInt, terms )
    }

  def name: Parser[String] = lower_word_or_integer | single_quoted

  def lower_word_or_integer: Parser[String] = """[a-z0-9_][A-Za-z0-9_-]*""".r

  def single_quoted: Parser[String] = "'" ~> """[^']*""".r <~ "'"

  def integer: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def comment: Parser[String] = """[%](.*)\n""".r ^^ { case s => "" }
}
