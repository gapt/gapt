package at.logic.gapt.formats.leanCoP

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.expansion.{ ExpansionTree, ExpansionSequent, formulaToExpansionTree }

import java.io.{ Reader, FileReader }
import scala.util.parsing.combinator._
import scala.collection.immutable.HashMap

class LeanCoPParserException( msg: String ) extends Exception( msg: String )
class LeanCoPNoMatchException( msg: String ) extends Exception( msg: String )
class LeanCoPNoLeanPredException( msg: String ) extends Exception( msg: String )
class LeanCoPLeanPredWrongArityException( msg: String ) extends Exception( msg: String )

object LeanCoPParser extends RegexParsers with PackratParsers {

  val nLine = sys.props( "line.separator" )

  def getExpansionProof( filename: String ): Option[ExpansionSequent] = {
    getExpansionProof( new FileReader( filename ) )
  }

  def getExpansionProof( reader: Reader ): Option[ExpansionSequent] = {
    parseAll( expansionSequent, reader ) match {
      case Success( r, _ ) => r
      case Failure( msg, next ) =>
        throw new LeanCoPParserException( "leanCoP parsing: syntax failure " + msg + nLine + "at line " + next.pos.line + " and column " + next.pos.column )
      case Error( msg, next ) =>
        throw new LeanCoPParserException( "leanCoP parsing: syntax error " + msg + nLine + "at line " + next.pos.line + " and column " + next.pos.column )
    }
  }

  // Restricted definitional clausal form (implemented by leanCoP)
  // Takes a formula in NNF and returns a list of clauses in DNF (possibly with
  // introduced definitions)
  // (reverse engineering leanCoP)
  def toDefinitionalClausalForm( f: FOLFormula, lean_preds: List[( String, Int )] ): List[FOLFormula] = {

    def toDCF( f: FOLFormula, lean_preds: List[( String, Int )], inConj: Boolean ): ( FOLFormula, List[FOLFormula] ) = f match {
      case FOLAtom( _, _ )        => ( f, List() )
      case Neg( FOLAtom( _, _ ) ) => ( f, List() )
      case And( f1, f2 ) =>
        val ( f1d, d1 ) = toDCF( f1, lean_preds, true )
        val used_preds = d1.flatMap( c => getLeanPreds( c ) )
        val rest = lean_preds.filter( p => !used_preds.contains( p ) )
        val ( f2d, d2 ) = toDCF( f2, rest, true )
        ( And( f1d, f2d ), d1 ++ d2 )
      case Or( f1, f2 ) => {
        if ( inConj ) {
          val vars = freeVariables( f ).toList

          val candidates = lean_preds.filter { case ( n, a ) => a == vars.length }
          val ordered_candidates = candidates.sorted

          if ( lean_preds.isEmpty ) {
            throw new LeanCoPNoLeanPredException( "Formula: " + f )
          }
          if ( candidates.isEmpty ) {
            throw new LeanCoPLeanPredWrongArityException( "Formula: " + f + " Candidates: " + lean_preds + " Arity: " + vars.length )
          }

          // Trusting that we have the same order as leanCoP
          val pred_name = ordered_candidates.head._1
          val new_pred = FOLAtom( pred_name, vars )
          val rest = lean_preds.filter { case ( n, a ) => n != pred_name }

          val ( f1d, d1 ) = toDCF( f1, rest, inConj )
          // TODO candidate for efficiency improvement
          val used_preds = d1.flatMap( c => getLeanPreds( c ) )
          val rest_of_rest = rest.filter( p => !used_preds.contains( p ) )
          val ( f2d, d2 ) = toDCF( f2, rest_of_rest, inConj )

          val def1 = And( Neg( new_pred ), f1d )
          val def2 = And( Neg( new_pred ), f2d )

          ( new_pred, def1 :: def2 :: d1 ++ d2 )

        } else {
          val ( f1d, d1 ) = toDCF( f1, lean_preds, inConj )
          val used_preds = d1.flatMap( c => getLeanPreds( c ) )
          val rest = lean_preds.filter( p => !used_preds.contains( p ) )
          val ( f2d, d2 ) = toDCF( f2, rest, inConj )
          ( Or( f1d, f2d ), d1 ++ d2 )
        }
      }
      case _ => throw new Exception( "Unsupported format for definitional clausal transformation: " + f )
    }

    val ( fd, defs ) = toDCF( f, lean_preds, false )
    fd :: defs.flatMap( d => DNFp.toFormulaList( d ) )
  }

  // Collects all n ^ [...] predicates used and their arities
  def getLeanPreds( cls: FOLFormula ): List[( String, Int )] = cls match {
    case FOLAtom( n, args ) if n.toString.startsWith( "leanP" ) => List( ( n.toString, args.length ) )
    case FOLAtom( _, _ ) => List()
    case Neg( f ) => getLeanPreds( f )
    case And( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case Or( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case _ => throw new Exception( "Unsupported format for getLeanPreds: " + cls )
  }

  def toMagicalDNF( f: FOLFormula ): List[FOLFormula] = {
    val normal_dnf = DNFp.toFormulaList( f )

    def collectLiterals( cls: FOLFormula ): List[FOLFormula] = cls match {
      case FOLAtom( _, _ )                        => List( cls )
      case Neg( FOLAtom( _, _ ) )                 => List( cls )
      case And( f1 @ FOLAtom( _, _ ), f2 )        => f1 :: collectLiterals( f2 )
      case And( f1 @ Neg( FOLAtom( _, _ ) ), f2 ) => f1 :: collectLiterals( f2 )
      case And( f1, f2 @ FOLAtom( _, _ ) )        => collectLiterals( f1 ) :+ f2
      case And( f1, f2 @ Neg( FOLAtom( _, _ ) ) ) => collectLiterals( f1 ) :+ f2
      case And( f1, f2 )                          => collectLiterals( f1 ) ++ collectLiterals( f2 )
      case _                                      => throw new Exception( "collectLiterals: formula " + cls + " is not a clause." )
    }

    normal_dnf.map( c => And( collectLiterals( c ) ) )
  }

  def matchClauses( my_clauses: List[FOLFormula], lean_clauses: List[FOLFormula] ): Option[FOLSubstitution] = {

    val num_clauses = lean_clauses.length
    val goal = Or.rightAssociative( lean_clauses: _* )

    // Get all sub-lists of my_clauses of size num_clauses
    val set_same_size = my_clauses.combinations( num_clauses )
    val candidates = set_same_size.flatMap( s => s.permutations.map( p => Or.rightAssociative( p: _* ) ) )

    def findSubstitution( lst: List[FOLFormula], goal: FOLFormula ): Option[FOLSubstitution] = lst match {
      case Nil => None
      case hd :: tl => FOLMatchingAlgorithm.matchTerms( hd, goal ) match {
        case None        => findSubstitution( tl, goal )
        case Some( sub ) => Some( sub )
      }
    }

    findSubstitution( candidates.toList, goal )
  }

  def expansionSequent: Parser[Option[ExpansionSequent]] =
    rep( comment ) ~> rep( input ) ~ rep( comment ) ~ rep( clauses ) ~ rep( comment ) ~ rep( inferences ) <~ rep( comment ) ^^ {
      case input ~ _ ~ clauses_lst ~ _ ~ bindings_opt =>

        if ( input.isEmpty && clauses_lst.isEmpty && bindings_opt.isEmpty ) None
        else {

          // Name -> (Formula, Role)
          val input_formulas0 = input.foldLeft( HashMap[String, ( FOLFormula, String )]() ) {
            case ( in_map, ( n, r, f ) ) => in_map + ( n -> ( f, r ) )
          }
          // Adding eq theory clauses to input formulas with names
          // lean_eq_theory_i
          val input_formulas = clauses_lst.foldLeft( input_formulas0 ) {
            case ( map, ( i, f, n ) ) =>
              if ( n == "lean_eq_theory" ) {
                val name = n + "_" + i
                map + ( name -> ( ( f, "axiom" ) ) )
              } else map
          }

          val clauses = clauses_lst.foldLeft( HashMap[Int, ( FOLFormula, String )]() ) {
            case ( map, ( i, f, n ) ) => map + ( i -> ( f, n ) )
          }
          val clauses_no_eq = clauses.filter { case ( i, ( f, n ) ) => n != "lean_eq_theory" }

          // String (name of input formula) -> List[Int] (all clauses generated from it)
          val formulas_to_clauses = clauses_no_eq.groupBy { case ( i, ( f, n ) ) => n }.map {
            case ( n, m ) => ( n, m.keys )
          }

          val bindings = bindings_opt.flatten

          // Int (number of clause) -> list of substitutions used
          val clauses_substitutions = bindings.groupBy( _._1 ).foldLeft( HashMap[Int, List[FOLSubstitution]]() ) {
            case ( map, ( i, lst ) ) =>
              val sublst = lst.map { case ( i, lvars, lterms ) => FOLSubstitution( lvars.zip( lterms ) ) }
              map + ( i -> sublst )
          }

          val formula_substitutions = formulas_to_clauses.foldLeft( HashMap[String, ( FOLFormula, List[FOLSubstitution] )]() ) {
            case ( map, ( name, lst_int ) ) =>

              val lean_clauses = lst_int.map( i => clauses( i )._1 ).toList
              // New predicates used in the def clausal translation and arity
              val lean_preds = lean_clauses.flatMap( c => getLeanPreds( c ) ).distinct

              val ( f_original, role ) = input_formulas( name )

              val f_right_pol = if ( role == "conjecture" ) f_original
              else Neg( f_original )

              val f_in_nnf = toNNF( f_right_pol )

              val f_no_quant = removeAllQuantifiers( f_in_nnf )

              // If there are not lean predicate symbols, use regular DNF transformation
              val subs = lean_preds match {
                case Nil =>
                  val f_dnf = toMagicalDNF( f_no_quant )
                  matchClauses( f_dnf, lean_clauses ) match {
                    case Some( s ) => s
                    case None => throw new LeanCoPNoMatchException( "leanCoP parsing: formula " + f_dnf +
                      " and clauses " + lean_clauses + " do not match [1]." )
                  }
                case _ :: _ =>
                  val f_clausified = toDefinitionalClausalForm( f_no_quant, lean_preds )
                  matchClauses( f_clausified, lean_clauses ) match {
                    case Some( s ) => s
                    case None => throw new LeanCoPNoMatchException( "leanCoP parsing: formula " + f_clausified +
                      " and clauses " + lean_clauses + " do not match [2]." )
                  }
              }

              val sublst = lst_int.flatMap( i => clauses_substitutions.get( i ) match {
                case Some( cs ) => cs.map( s => s.compose( subs ) )
                case None       => List( subs )
              } ).toList
              map + ( name -> ( ( f_original, sublst ) ) )
          }

          val ( ant, succ ) = formula_substitutions.foldLeft( ( List[ExpansionTree](), List[ExpansionTree]() ) ) {
            case ( ( a, s ), ( name, ( form, sublst ) ) ) =>
              val pos = if ( input_formulas( name )._2 == "axiom" ) false else true;
              val et = formulaToExpansionTree( form, sublst, pos )
              if ( pos ) ( a, ( et :: s ) )
              else ( ( et :: a ), s )
          }

          Some( new ExpansionSequent( ant, succ ) )
        }
    }

  def input: Parser[( String, String, FOLFormula )] = language ~ "(" ~> name ~ "," ~ role ~ "," ~ formula <~ ", file(" ~ "[^()]*".r ~ "))." ^^ {
    case n ~ _ ~ r ~ _ ~ f => ( n, r, f )
  }
  def clauses: Parser[( Int, FOLFormula, String )] = language ~ "(" ~> integer ~ ", plain," ~ clause ~ ", clausify(" ~ name <~ "))." ^^ {
    case i ~ _ ~ f ~ _ ~ n =>
      assert( n != "lean_eq_theory" )
      ( i, f, n )
  } | language ~ "(" ~> integer ~ ", plain," ~ clause <~ ", theory(equality))." ^^ {
    // Equality theory added by leanCoP
    case i ~ _ ~ f => ( i, f, "lean_eq_theory" )
  }

  def inferences: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = language ~ "(" ~ name ~ ",plain," ~ clause ~ "," ~> info <~ ")." ^^ {
    case bindings => bindings
  }

  def language: Parser[String] = "fof" | "cnf"
  def role: Parser[String] = "axiom" | "conjecture" | "lemma" | "hypothesis"

  def info: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = start | start_bind | reduction | extension | ext_w_bind

  def start: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "start(" ~> integer <~ ")" ^^ { case _ => None }
  def start_bind: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "start(" ~> integer ~ ",bind(" ~ list_subs <~ "))" ^^ {
    case n ~ _ ~ ls => Some( ( n, ls._1, ls._2 ) )
  }
  def reduction: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "reduction('" ~> integer <~ "')" ^^ { case _ => None }
  def extension: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "extension(" ~> integer <~ ")" ^^ { case _ => None }
  def ext_w_bind: Parser[Option[( Int, List[FOLVar], List[FOLTerm] )]] = "extension(" ~> integer ~ ",bind(" ~ list_subs <~ "))" ^^ {
    case n ~ _ ~ ls => Some( ( n, ls._1, ls._2 ) )
  }

  def list_subs: Parser[( List[FOLVar], List[FOLTerm] )] = "[[" ~> repsep( variable, "," ) ~ "], [" ~ repsep( term, "," ) <~ "]]" ^^ {
    case t ~ _ ~ v => ( t, v )
  }

  def clause: Parser[FOLFormula] = "[" ~> repsep( formula, "," ) <~ "]" ^^ {
    case formulas => And( formulas )
  }

  lazy val formula: PackratParser[FOLFormula] = dbl_impl

  lazy val dbl_impl: PackratParser[FOLFormula] = (
    impl ~ "<=>" ~ dbl_impl ^^ {
      case f1 ~ _ ~ f2 =>
        And( Or( Neg( f1 ), f2 ), Or( f1, Neg( f2 ) ) )
    }
    | impl
  )

  lazy val impl: PackratParser[FOLFormula] = (
    and ~ "=>" ~ impl ^^ { case f1 ~ _ ~ f2 => Imp( f1, f2 ) }
    | and
  )

  lazy val and: PackratParser[FOLFormula] = (
    or ~ "&" ~ and ^^ { case f1 ~ _ ~ f2 => And( f1, f2 ) }
    | or
  )

  lazy val or: PackratParser[FOLFormula] = (
    neg ~ "|" ~ or ^^ { case f1 ~ _ ~ f2 => Or( f1, f2 ) }
    | neg
  )

  lazy val neg: PackratParser[FOLFormula] = (
    ( "-" | "~" ) ~> neg ^^ { case f => Neg( f ) }
    | quantified
  )

  lazy val quantified: PackratParser[FOLFormula] = (
    "!" ~ "[" ~> repsep( variable, "," ) ~ "] : " ~ quantified ^^ {
      case vars ~ _ ~ form =>
        vars.foldLeft( form )( ( f, v ) => All( v, f ) )
    }
    | "?" ~ "[" ~> repsep( variable, "," ) ~ "] : " ~ quantified ^^ {
      case vars ~ _ ~ form =>
        vars.foldLeft( form )( ( f, v ) => Ex( v, f ) )
    }
    | neg | atom
  )

  lazy val atom: PackratParser[FOLFormula] = not_eq | eq | lean_atom | real_atom | quantified | "(" ~> formula <~ ")"
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
  lazy val not_eq: PackratParser[FOLFormula] = "(!" ~> term ~ ")" ~ "=" ~ term ^^ {
    case t1 ~ _ ~ _ ~ t2 => Neg( FOLAtom( "=", List( t1, t2 ) ) )
  }

  def term: Parser[FOLTerm] = skolem_term | variable | function | constant
  def function: Parser[FOLTerm] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ { case f ~ _ ~ args => FOLFunction( f, args ) }
  def constant: Parser[FOLConst] = name ^^ { case n => FOLConst( n ) }
  def variable: Parser[FOLVar] = """_[A-Z0-9]+""".r ^^ { case n => FOLVar( n ) }
  def skolem_term: Parser[FOLTerm] = lean_var ^^ {
    case ( i, _ ) =>
      // Pretend it's an eigenvariable.
      FOLVar( "leanSk" + i )
  }
  def lean_var: Parser[( Int, List[FOLTerm] )] = """\d+""".r ~ "^" ~ "[" ~ repsep( term, "," ) ~ "]" ^^ {
    case i ~ _ ~ _ ~ terms ~ _ => ( i.toInt, terms )
  }

  def name: Parser[String] = lower_word_or_integer | single_quoted
  def lower_word_or_integer: Parser[String] = """[a-z0-9_-][A-Za-z0-9_-]*""".r
  def single_quoted: Parser[String] = "'" ~> """[^']*""".r <~ "'"
  def integer: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def comment: Parser[String] = """[%](.*)\n""".r ^^ { case s => "" }
}
