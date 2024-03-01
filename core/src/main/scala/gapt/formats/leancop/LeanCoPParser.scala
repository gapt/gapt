package gapt.formats.leancop

import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol._
import gapt.expr.subst.FOLSubstitution
import gapt.expr.util.freeVariables
import gapt.formats.InputFile
import gapt.logic.Polarity
import gapt.logic.clauseSubsumption
import gapt.logic.hol.CNFn
import gapt.logic.hol.DNFp
import gapt.logic.hol.toNNF
import gapt.proofs.RichFOLSequent
import gapt.proofs.expansion.ExpansionSequent
import gapt.proofs.expansion.formulaToExpansionTree

import java.io.Reader
import java.io.StringReader
import scala.collection.mutable
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.RegexParsers

class LeanCoPParserException( msg: String ) extends Exception( msg: String )
class LeanCoPNoMatchException( msg: String ) extends Exception( msg: String )
class LeanCoPNoLeanPredException( msg: String ) extends Exception( msg: String )
class LeanCoPLeanPredWrongArityException( msg: String ) extends Exception( msg: String )

object LeanCoPParser extends RegexParsers with PackratParsers {

  override def skipWhitespace: Boolean = true

  private val nLine = sys.props( "line.separator" )

  def getExpansionProof( file: InputFile ): Option[ExpansionSequent] = {
    getExpansionProof( new StringReader( file.read ) )
  }

  def getExpansionProof( reader: Reader ): Option[ExpansionSequent] = {
    parseAll( expansionSequent, reader ) match {
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

  case class InputFormula( name: Name, role: Role, formula: FOLFormula )
  case class Clause( index: ClauseIndex, cls: FOLFormula, origin: Name )

  def constructExpansionSequent(
    inputs:   List[InputFormula],
    clauses:  List[Clause],
    bindings: List[( ClauseIndex, FOLSubstitution )] ): ExpansionSequent = {

    val initialFormula: Map[Name, InputFormula] =
      ( inputs ++
        clauses.collect {
          case Clause( i, f, n @ "lean_eq_theory" ) => InputFormula( n + "_" + i, "axiom", f )
        } ).map { i => i.name -> i } toMap

    val derivedClauses: List[Clause] =
      clauses.filter { _.origin != "lean_eq_theory" }

    val children: Map[Name, Iterable[Clause]] =
      derivedClauses.groupBy( _.origin )

    val substitutions: Map[ClauseIndex, List[FOLSubstitution]] =
      bindings.groupMap( _._1 )( _._2 )

    // Instances of the original formula of the given name.
    val instances: Map[Name, List[FOLSubstitution]] =
      children map {
        case ( name, lst_int ) =>
          val leanClauses = lst_int.map( _.cls ).toList
          // New predicates used in the def clausal translation and arity
          val leanPredicates = leanClauses.flatMap( c => getLeanPreds( c ) ).distinct
          val f_clausified = clausifyInitialFormula( initialFormula( name ), leanPredicates )
          val subs = matchClauses( f_clausified, leanClauses ) match {
            case Some( s ) => s
            case None => throw new LeanCoPNoMatchException( "leanCoP parsing: formula " + f_clausified +
              " and clauses " + leanClauses + " do not match." )
          }
          val sublst = lst_int.flatMap( i => substitutions.get( i.index ) match {
            case Some( cs ) => cs.map( s => s.compose( subs ) )
            case None       => List( subs )
          } ).toList
          name -> sublst
      }
    val polarizedETs = instances.map {
      case ( name, sublst ) =>
        val f = initialFormula( name )
        val p = polarityByRole( f.role )
        formulaToExpansionTree( f.formula, sublst, p ) -> p
    }

    ExpansionSequent( polarizedETs )
  }

  // Collects all n ^ [...] predicates used and their arities
  def getLeanPreds( cls: FOLFormula ): List[( String, Int )] = cls match {
    case FOLAtom( n, args ) if n.startsWith( "leanP" ) => List( ( n, args.length ) )
    case FOLAtom( _, _ ) => List()
    case Neg( f ) => getLeanPreds( f )
    case And( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case Or( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case _ => throw new Exception( "Unsupported format for getLeanPreds: " + cls )
  }

  /**
   * Clausifies the given formula.
   *
   * The clausification makes use of the predicate symbols introduced by LeanCoP.
   */
  def clausifyInitialFormula( f: InputFormula, leanPredicates: List[LeanPredicate] ): List[FOLFormula] = {
    val InputFormula( _, role, f_original ) = f
    val f_right_pol =
      if ( role == "conjecture" ) f_original
      else Neg( f_original )
    val f_in_nnf = toNNF( f_right_pol )
    val f_no_quant = removeAllQuantifiers( f_in_nnf )
    // If there are not lean predicate symbols, use regular DNF transformation
    leanPredicates match {
      case Seq() => toMagicalDNF( f_no_quant )
      case _     => toDefinitionalClausalForm( f_no_quant, leanPredicates )
    }
  }

  def toMagicalDNF( f: FOLFormula ): List[FOLFormula] = {
    val normal_dnf = DNFp( f )
    normal_dnf.map( _.toConjunction ).toList
  }

  /**
   * Computes the definitional clausal form of a given formula.
   *
   * @param f The formula in NNF whose DCF is to be constructed.
   * @param leanPredicates The predicates available for the DCF construction.
   * @return A list list of clauses in DNF (possibly with introduced definitions) corresponding to the
   *         definitional clausal form of the input formula
   */
  def toDefinitionalClausalForm( f: FOLFormula, leanPredicates: List[LeanPredicate] ): List[FOLFormula] = {

    type DefinitionalTuple = ( FOLFormula, List[FOLFormula] )

    var unusedPredicates: mutable.Set[LeanPredicate] = mutable.Set( leanPredicates: _* )

    def definitionalTuple( f: FOLFormula, insideConjunction: Boolean ): DefinitionalTuple =
      f match {
        case FOLLiteral( _, _ ) => ( f, List() )
        case Or( f1, f2 ) if insideConjunction => {
          val xs = freeVariables( f )
          getUnusedPredicate( xs.size ) match {
            case Some( p ) =>
              // Trusting that we have the same order as leanCoP
              val pxs = FOLAtom( p._1, xs.toList )
              unusedPredicates -= p
              val ( f1d, d1 ) = definitionalTuple( f1, insideConjunction )
              val ( f2d, d2 ) = definitionalTuple( f2, insideConjunction )
              ( pxs, ( -pxs & f1d ) :: ( -pxs & f2d ) :: d1 ++ d2 )
            case _ => throw new LeanCoPLeanPredWrongArityException(
              "Formula: " + f + " Candidates: " + unusedPredicates + " Arity: " + xs.size )
          }
        }
        case And( f1, f2 ) =>
          val ( f1d, d1 ) = definitionalTuple( f1, true )
          val ( f2d, d2 ) = definitionalTuple( f2, true )
          ( And( f1d, f2d ), d1 ++ d2 )
        case Or( f1, f2 ) =>
          val ( f1d, d1 ) = definitionalTuple( f1, insideConjunction )
          val ( f2d, d2 ) = definitionalTuple( f2, insideConjunction )
          ( Or( f1d, f2d ), d1 ++ d2 )
        case _ => throw new Exception( "Unsupported format for definitional clausal transformation: " + f )
      }

    /*
     * Retrieves a currently unused predicate of the given arity.
     * @param n The arity of the predicate.
     */
    def getUnusedPredicate( n: Int ): Option[LeanPredicate] =
      unusedPredicates.collectFirst { case p @ ( _, `n` ) => p }

    val ( fd, defs ) = definitionalTuple( f, false )
    fd :: defs.flatMap( d => DNFp( d ).map( _.toConjunction ) )
  }

  def matchClauses( my_clauses: List[FOLFormula], lean_clauses: List[FOLFormula] ): Option[FOLSubstitution] = {
    val num_clauses = lean_clauses.length
    val goal = Or.rightAssociative( lean_clauses: _* )

    // Get all sub-lists of my_clauses of size num_clauses
    val set_same_size = my_clauses.combinations( num_clauses )
    val candidates = set_same_size.flatMap( s => s.permutations.map( p => Or.rightAssociative( p: _* ) ) )

    def findSubstitution( lst: List[FOLFormula], goal: FOLFormula ): Option[FOLSubstitution] = lst match {
      case Nil => None
      case hd :: tl => clauseSubsumption( CNFn( hd ).head, CNFn( goal ).head ) match {
        case None        => findSubstitution( tl, goal )
        case Some( sub ) => Some( sub.asFOLSubstitution )
      }
    }

    findSubstitution( candidates.toList, goal )
  }

  def expansionSequent: Parser[Option[ExpansionSequent]] =
    rep( comment ) ~>
      rep( input ) ~ rep( comment ) ~ rep( clauses ) ~ rep( comment ) ~ rep( inferences ) <~
      rep( comment ) ^^ {
        case Seq() ~ _ ~ Seq() ~ _ ~ Seq() =>
          None
        case input ~ _ ~ clauses_lst ~ _ ~ bindings_opt =>
          val inputs = input.map { case ( n, r, f ) => InputFormula( n, r, f ) }
          val clauses = clauses_lst.map { case ( i, f, n ) => Clause( i, f, n ) }
          val bindings = bindings_opt.flatten.map { case ( i, vs, ts ) => i -> FOLSubstitution( vs.zip( ts ) ) }
          Some( constructExpansionSequent( inputs, clauses, bindings ) )
      }

  def polarityByRole( r: Role ): Polarity =
    r match {
      case "axiom" => Polarity.InAntecedent
      case _       => Polarity.InSuccedent
    }

  def input: Parser[( String, String, FOLFormula )] =
    language ~ "(" ~>
      name ~ "," ~ role ~ "," ~ formula <~
      "," ~ "file" ~ "(" ~ "[^()]*".r ~ ")" ~ ")" ~ "." ^^ {
        case n ~ _ ~ r ~ _ ~ f => ( n, r, f )
      }

  def clauses: Parser[( Int, FOLFormula, String )] =
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

  def clause: Parser[FOLFormula] =
    "[" ~> repsep( formula, "," ) <~ "]" ^^ {
      case formulas => And( formulas )
    }

  lazy val formula: PackratParser[FOLFormula] = dbl_impl

  lazy val dbl_impl: PackratParser[FOLFormula] = (
    impl ~ "<=>" ~ dbl_impl ^^ {
      case f1 ~ _ ~ f2 =>
        And( Or( Neg( f1 ), f2 ), Or( f1, Neg( f2 ) ) )
    }
    | impl )

  lazy val impl: PackratParser[FOLFormula] = (
    and ~ "=>" ~ impl ^^ { case f1 ~ _ ~ f2 => Imp( f1, f2 ) }
    | and )

  lazy val and: PackratParser[FOLFormula] = (
    or ~ "&" ~ and ^^ { case f1 ~ _ ~ f2 => And( f1, f2 ) }
    | or )

  lazy val or: PackratParser[FOLFormula] = (
    neg ~ "|" ~ or ^^ { case f1 ~ _ ~ f2 => Or( f1, f2 ) }
    | neg )

  lazy val neg: PackratParser[FOLFormula] = (
    ( "-" | "~" ) ~> neg ^^ { case f => Neg( f ) }
    | quantified )

  lazy val quantified: PackratParser[FOLFormula] = (
    "!" ~ "[" ~> repsep( variable, "," ) ~ "]" ~ ":" ~ quantified ^^ {
      case vs ~ _ ~ _ ~ f => All.Block( vs, f )
    }
    | "?" ~ "[" ~> repsep( variable, "," ) ~ "]" ~ ":" ~ quantified ^^ {
      case vs ~ _ ~ _ ~ f => Ex.Block( vs, f )
    }
    | neg | atom )

  lazy val atom: PackratParser[FOLFormula] =
    not_eq | eq | lean_atom | real_atom | quantified | "(" ~> formula <~ ")"

  // These are introduced by leanCoP's (restricted) definitional clausal form translation
  lazy val lean_atom: PackratParser[FOLFormula] = lean_var ^^ {
    case ( i, terms ) =>
      FOLAtom( "leanP" + i, terms )
  }

  lazy val real_atom: PackratParser[FOLFormula] = name ~ opt( "(" ~> repsep( term, "," ) <~ ")" ) ^^ {
    case pred ~ Some( args ) => FOLAtom( pred, args )
    case pred ~ None         => FOLAtom( pred )
  }

  lazy val eq: PackratParser[FOLFormula] = term ~ "=" ~ term ^^ {
    case t1 ~ _ ~ t2 => FOLAtom( "=", List( t1, t2 ) )
  }

  lazy val not_eq: PackratParser[FOLFormula] = "(" ~ "!" ~> term ~ ")" ~ "=" ~ term ^^ {
    case t1 ~ _ ~ _ ~ t2 => Neg( FOLAtom( "=", List( t1, t2 ) ) )
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

  def lower_word_or_integer: Parser[String] = """[a-z0-9_-][A-Za-z0-9_-]*""".r

  def single_quoted: Parser[String] = "'" ~> """[^']*""".r <~ "'"

  def integer: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def comment: Parser[String] = """[%](.*)\n""".r ^^ { case s => "" }
}
