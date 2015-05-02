package at.logic.gapt.formats.leanCoP

import at.logic.gapt.proofs.expansionTrees.{ ExpansionTree, ExpansionSequent, formulaToExpansionTree }
import at.logic.gapt.language.fol._

import java.io.{ Reader, FileReader }
import scala.util.parsing.combinator._
import scala.collection.immutable.HashMap

object LeanCoPParser extends RegexParsers with PackratParsers {

  def getExpansionProof( filename: String ): ExpansionSequent = {
    getExpansionProof( new FileReader( filename ) )
  }

  def getExpansionProof( reader: Reader ): ExpansionSequent = {
    parseAll( expansionSequent, reader ) match {
      case Success( r, _ ) => r
      case Failure( msg, next ) =>
        throw new Exception( "leanCoP parsing: syntax failure " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column )
      case Error( msg, next ) =>
        throw new Exception( "leanCoP parsing: syntax error " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column )
    }
  }

  def expansionSequent: Parser[ExpansionSequent] =
    rep( comment ) ~> rep( input ) ~ comment ~ rep( clauses ) ~ comment ~ rep( inferences ) <~ rep( comment ) ^^ {
      case input ~ _ ~ clauses ~ _ ~ bindings =>

        val endsequent = input.foldLeft( ( List[FOLFormula](), List[FOLFormula]() ) ) {
          case ( acc, ( n, r, f ) ) =>
            if ( r == "conjecture" ) ( acc._1, f :: acc._2 )
            else if ( r == "axiom" ) ( f :: acc._1, acc._2 )
            else throw new Exception( "Lemma and hypothesis?" );
        }

        val bindmap = bindings.foldLeft( HashMap[Int, List[FOLSubstitution]]() ) {
          case ( acc, b ) => b match {
            case Some( ( n, lvars, lterms ) ) =>
              assert( lvars.length == lterms.length )
              val subs = FOLSubstitution( lvars.zip( lterms ) )
              acc.get( n ) match {
                case Some( s ) => acc + ( ( n, subs :: s ) )
                case None      => acc + ( ( n, List( subs ) ) )
              }
            case None => acc
          }
        }

        // TODO map clauses to input formula. Currently using clauses as the end-sequent
        val clausified_succ = clauses.map {
          case ( i, f, n ) =>
            // Every variable is implicitly universally quantified, here we add the
            // quantifier by hand
            val vars = freeVariables( f )
            val quantified = addQuantifiers( f, vars )
            bindmap.get( i ) match {
              case Some( sublst ) =>
                formulaToExpansionTree( quantified, sublst, true )
              case None => formulaToExpansionTree( f, true )
            }
        }

        new ExpansionSequent( Nil, clausified_succ )
    }

  def input: Parser[( String, String, FOLFormula )] = language ~ "(" ~> name ~ "," ~ role ~ "," ~ formula <~ ", file(" ~ "[^()]*".r ~ "))." ^^ {
    case n ~ _ ~ r ~ _ ~ f => ( n, r, f )
  }
  def clauses: Parser[( Int, FOLFormula, String )] = language ~ "(" ~> integer ~ ", plain," ~ clause ~ ", clausify(" ~ name <~ "))." ^^ {
    case i ~ _ ~ f ~ _ ~ n => ( i, f, n )
  }
  def inferences: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = language ~ "(" ~ name ~ ",plain," ~ clause ~ "," ~> info <~ ")." ^^ {
    case bindings => bindings
  }

  def language: Parser[String] = "fof" | "cnf"
  def role: Parser[String] = "axiom" | "conjecture" | "lemma" | "hypothesis"

  def info: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = start | reduction | extension | ext_w_bind

  def start: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "start(" ~> integer <~ ")" ^^ { case _ => None }
  def reduction: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "reduction('" ~> integer <~ "')" ^^ { case _ => None }
  def extension: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "extension(" ~> integer <~ ")" ^^ { case _ => None }
  def ext_w_bind: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "extension(" ~> integer ~ ",bind(" ~ list_subs <~ "))" ^^ {
    case n ~ _ ~ ls => Some( ( n, ls._1, ls._2 ) )
  }

  def list_subs: Parser[( List[FOLVar], List[FOLTerm] )] = "[[" ~> repsep( variable, "," ) ~ "], [" ~ repsep( term, "," ) <~ "]]" ^^ {
    case t ~ _ ~ v => ( t, v )
  }

  def clause: Parser[FOLFormula] = "[" ~> repsep( formula, "," ) <~ "]" ^^ { case formulas => FOLOr( formulas ) }

  lazy val formula: PackratParser[FOLFormula] = opt( "(" ) ~> ( atom | neg | and | or | impl | forall | exists ) <~ opt( ")" )

  def term: Parser[FOLTerm] = variable | function | constant
  def function: Parser[FOLTerm] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ { case f ~ _ ~ args => FOLFunction( f, args ) }
  def constant: Parser[FOLConst] = name ^^ { case n => FOLConst( n ) }
  // Variables in leanCoP are always of the shape _[1-9]+
  def variable: Parser[FOLVar] = """_[0-9]+""".r ^^ { case n => FOLVar( n ) }
  // TODO n ^ [...] terms

  lazy val atom: PackratParser[FOLFormula] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ { case pred ~ _ ~ args => FOLAtom( pred, args ) }
  lazy val neg: PackratParser[FOLFormula] = "~" ~> formula ^^ { case f => FOLNeg( f ) }
  lazy val and: PackratParser[FOLFormula] = formula ~ "&" ~ formula ^^ { case f1 ~ _ ~ f2 => FOLAnd( f1, f2 ) }
  lazy val or: PackratParser[FOLFormula] = formula ~ "|" ~ formula ^^ { case f1 ~ _ ~ f2 => FOLOr( f1, f2 ) }
  lazy val impl: PackratParser[FOLFormula] = formula ~ "=>" ~ formula ^^ { case f1 ~ _ ~ f2 => FOLImp( f1, f2 ) }
  lazy val forall: PackratParser[FOLFormula] = "!" ~ "[" ~> variable ~ "] :" ~ formula ^^ { case v ~ _ ~ f => FOLAllVar( v, f ) }
  lazy val exists: PackratParser[FOLFormula] = "?" ~ "[" ~> variable ~ "] :" ~ formula ^^ { case v ~ _ ~ f => FOLExVar( v, f ) }

  def name: Parser[String] = """[^ ():,!?\[\]~&|=>]+""".r ^^ { case s => s }
  def integer: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def comment: Parser[String] = """[%](.*)\n""".r ^^ { case s => "" }
}
