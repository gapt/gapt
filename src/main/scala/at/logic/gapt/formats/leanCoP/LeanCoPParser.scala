package at.logic.gapt.formats.leanCoP

import at.logic.gapt.proofs.expansionTrees.{ ExpansionTree, ExpansionSequent, formulaToExpansionTree }
import at.logic.gapt.language.fol._
import at.logic.gapt.language.fol.algorithms.FOLMatchingAlgorithm

import java.io.{ Reader, FileReader }
import scala.util.parsing.combinator._
import scala.collection.immutable.HashMap

class LeanCoPParserException( msg: String ) extends Exception( msg: String )
class LeanCoPNoMatchException( msg: String ) extends Exception( msg: String )
class LeanCoPNoLeanPredException( msg: String ) extends Exception( msg: String )

object LeanCoPParser extends RegexParsers with PackratParsers {

  def getExpansionProof( filename: String ): Option[ExpansionSequent] = {
    getExpansionProof( new FileReader( filename ) )
  }

  def getExpansionProof( reader: Reader ): Option[ExpansionSequent] = {
    parseAll( expansionSequent, reader ) match {
      case Success( r, _ ) => r
      case Failure( msg, next ) =>
        throw new LeanCoPParserException( "leanCoP parsing: syntax failure " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column )
      case Error( msg, next ) =>
        throw new LeanCoPParserException( "leanCoP parsing: syntax error " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column )
    }
  }

  // Restricted definitional clausal form (implemented by leanCoP)
  // Takes a formula in NNF and returns a list of clauses in DNF (possibly with
  // introduced definitions)
  // (reverse engineering leanCoP)
  def toDefinitionalClausalForm( f: FOLFormula, lean_preds: List[( String, Int )] ): List[FOLFormula] = {

    def toDCF( f: FOLFormula, lean_preds: List[( String, Int )], inConj: Boolean ): ( FOLFormula, List[FOLFormula] ) = f match {
      case FOLAtom( _, _ )           => ( f, List() )
      case FOLNeg( FOLAtom( _, _ ) ) => ( f, List() )
      case FOLAnd( f1, f2 ) =>
        val ( f1d, d1 ) = toDCF( f1, lean_preds, true )
        val used_preds = d1.flatMap( c => getLeanPreds( c ) )
        val rest = lean_preds.filter( p => !used_preds.contains( p ) )
        val ( f2d, d2 ) = toDCF( f2, rest, true )
        ( FOLAnd( f1d, f2d ), d1 ++ d2 )
      case FOLOr( f1, f2 ) => {
        if ( inConj ) {

          val vars = freeVariables( f )

          val candidates = lean_preds.filter { case ( n, a ) => a == vars.length }
          val ordered_candidates = candidates.sorted

          if ( candidates.isEmpty ) {
            throw new LeanCoPNoLeanPredException( "Formula: " + f + " Candidates: " + lean_preds )
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

          val def1 = FOLAnd( FOLNeg( new_pred ), f1d )
          val def2 = FOLAnd( FOLNeg( new_pred ), f2d )

          ( new_pred, def1 :: def2 :: d1 ++ d2 )

        } else {
          val ( f1d, d1 ) = toDCF( f1, lean_preds, inConj )
          val used_preds = d1.flatMap( c => getLeanPreds( c ) )
          val rest = lean_preds.filter( p => !used_preds.contains( p ) )
          val ( f2d, d2 ) = toDCF( f2, rest, inConj )
          ( FOLOr( f1d, f2d ), d1 ++ d2 )
        }
      }
      case _ => throw new Exception( "Unsupported format for definitional clausal transformation: " + f )
    }

    val ( fd, defs ) = toDCF( f, lean_preds, false )
    fd :: defs.flatMap( d => toDNF( d ) )
  }

  // Polarity is true for positive and false for negative
  def skolemizeWith( f: FOLFormula, sk_functions: List[( String, Int )], polarity: Boolean ): FOLFormula = {

    def skWith( f: FOLFormula, terms: List[FOLVar], sk_functions: List[( String, Int )], polarity: Boolean ): FOLFormula = f match {
      case FOLAtom( _, _ ) => f
      case FOLNeg( f1 )    => FOLNeg( skWith( f1, terms, sk_functions, !polarity ) )
      case FOLImp( f1, f2 ) =>
        val f1sk = skWith( f1, terms, sk_functions, !polarity )
        // TODO candidate for efficiency improvement
        val used = getSkFunctions( f1sk )
        val rest = sk_functions.filter( f => !used.contains( f ) )
        val f2sk = skWith( f2, terms, rest, polarity )
        FOLImp( f1sk, f2sk )
      case FOLAnd( f1, f2 ) =>
        val f1sk = skWith( f1, terms, sk_functions, polarity )
        // TODO candidate for efficiency improvement
        val used = getSkFunctions( f1sk )
        val rest = sk_functions.filter( f => !used.contains( f ) )
        val f2sk = skWith( f2, terms, rest, polarity )
        FOLAnd( f1sk, f2sk )
      case FOLOr( f1, f2 ) =>
        val f1sk = skWith( f1, terms, sk_functions, polarity )
        // TODO candidate for efficiency improvement
        val used = getSkFunctions( f1sk )
        val rest = sk_functions.filter( f => !used.contains( f ) )
        val f2sk = skWith( f2, terms, rest, polarity )
        FOLOr( f1sk, f2sk )
      case FOLExVar( x, f1 ) => polarity match {
        case true => // Weak quantifier
          FOLExVar( x, skWith( f1, terms :+ x, sk_functions, polarity ) )
        case false => // Strong quantifier
          val candidates = sk_functions.filter { case ( n, a ) => a == terms.size }
          val ordered_candidates = candidates.sorted

          val fun_name = ordered_candidates.head._1
          val sk_func = FOLFunction( fun_name, terms )
          val rest = sk_functions.filter { case ( n, a ) => n != fun_name }

          val sub = FOLSubstitution( x, sk_func )
          val f1sk = sub( f1 )
          skWith( f1sk, terms, rest, polarity )
      }
      case FOLAllVar( x, f1 ) => polarity match {
        case true => // Strong quantifier
          val candidates = sk_functions.filter { case ( n, a ) => a == terms.size }
          val ordered_candidates = candidates.sorted

          val fun_name = ordered_candidates.head._1
          val sk_func = FOLFunction( fun_name, terms )
          val rest = sk_functions.filter { case ( n, a ) => n != fun_name }

          val sub = FOLSubstitution( x, sk_func )
          val f1sk = sub( f1 )
          skWith( f1sk, terms, rest, polarity )
        case false => // Weak quantifier
          FOLAllVar( x, skWith( f1, terms :+ x, sk_functions, polarity ) )
      }
    }

    skWith( f, List(), sk_functions, polarity )
  }

  // Collects all n ^ [...] predicates used and their arities
  def getLeanPreds( cls: FOLFormula ): List[( String, Int )] = cls match {
    case FOLAtom( n, args ) if n.toString.startsWith( "leanP" ) => List( ( n.toString, args.length ) )
    case FOLAtom( _, _ ) => List()
    case FOLNeg( f ) => getLeanPreds( f )
    case FOLAnd( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case FOLOr( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case _ => throw new Exception( "Unsupported format for getLeanPreds: " + cls )
  }

  // Collects all n ^ [...] functions used for skolemization and their arities
  def getSkFunctions( cls: FOLExpression ): List[( String, Int )] = cls match {
    case FOLFunction( n, args ) if n.toString.startsWith( "leanSk" ) => List( ( n.toString, args.length ) )
    case FOLFunction( _, args ) => args.flatMap( a => getSkFunctions( a ) )
    case FOLVar( _ ) => List()
    case FOLConst( n ) if n.toString.startsWith( "leanSk" ) => List( ( n.toString, 0 ) )
    case FOLConst( _ ) => List()
    case FOLAtom( _, args ) => args.flatMap( a => getSkFunctions( a ) )
    case FOLNeg( f ) => getSkFunctions( f )
    case FOLAnd( f1, f2 ) => getSkFunctions( f1 ) ++ getSkFunctions( f2 )
    case FOLOr( f1, f2 ) => getSkFunctions( f1 ) ++ getSkFunctions( f2 )
    case FOLExVar( x, f1 ) => getSkFunctions( f1 )
    case FOLAllVar( x, f1 ) => getSkFunctions( f1 )
    case _ => throw new Exception( "Unsupported format for getSkFunctions: " + cls )
  }

  // leanCoP renames all variables so that they do not clash.
  def dropQuantifiers( f: FOLFormula ): FOLFormula = f match {
    case FOLAtom( _, _ )    => f
    case FOLNeg( f1 )       => FOLNeg( dropQuantifiers( f1 ) )
    case FOLImp( f1, f2 )   => FOLImp( dropQuantifiers( f1 ), dropQuantifiers( f2 ) )
    case FOLAnd( f1, f2 )   => FOLAnd( dropQuantifiers( f1 ), dropQuantifiers( f2 ) )
    case FOLOr( f1, f2 )    => FOLOr( dropQuantifiers( f1 ), dropQuantifiers( f2 ) )
    case FOLExVar( x, f1 )  => dropQuantifiers( f1 )
    case FOLAllVar( x, f1 ) => dropQuantifiers( f1 )
  }

  def toMagicalDNF( f: FOLFormula ): List[FOLFormula] = {
    val normal_dnf = toDNF( f )

    def collectLiterals( cls: FOLFormula ): List[FOLFormula] = cls match {
      case FOLAtom( _, _ ) => List( cls )
      case FOLNeg( FOLAtom( _, _ ) ) => List( cls )
      case FOLAnd( f1 @ FOLAtom( _, _ ), f2 ) => f1 :: collectLiterals( f2 )
      case FOLAnd( f1 @ FOLNeg( FOLAtom( _, _ ) ), f2 ) => f1 :: collectLiterals( f2 )
      case FOLAnd( f1, f2 @ FOLAtom( _, _ ) ) => f2 :: collectLiterals( f1 )
      case FOLAnd( f1, f2 @ FOLNeg( FOLAtom( _, _ ) ) ) => f2 :: collectLiterals( f1 )
      case FOLAnd( f1, f2 ) => collectLiterals( f1 ) ++ collectLiterals( f2 )
      case _ => throw new Exception( "collectLiterals: formula " + cls + " is not a clause." )
    }

    normal_dnf.map( c => FOLAnd( collectLiterals( c ) ) )
  }

  def matchClauses( my_clauses: List[FOLFormula], lean_clauses: List[FOLFormula] ): Option[FOLSubstitution] = {

    val num_clauses = lean_clauses.length
    val goal = FOLOr.rightAssociative( lean_clauses )

    // Get all sub-lists of my_clauses of size num_clauses
    val set_same_size = my_clauses.combinations( num_clauses )
    val candidates = set_same_size.flatMap( s => s.permutations.map( p => FOLOr.rightAssociative( p ) ) )

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
    rep( comment ) ~> rep( input ) ~ comment ~ rep( clauses ) ~ comment ~ rep( inferences ) <~ rep( comment ) ^^ {
      case input ~ _ ~ clauses_lst ~ _ ~ bindings_opt =>

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
            // Skolem terms used in skolemization and arity
            val skolem_functions = lean_clauses.flatMap( c => getSkFunctions( c ) ).distinct

            val ( f_original, role ) = input_formulas( name )

            val f_right_pol = if ( role == "conjecture" ) f_original
            else FOLNeg( f_original )

            val f_in_nnf = toNNF( f_right_pol )

            // All formulas are on the left side of the sequent for leanCoP
            val f_skolemized = skolem_functions match {
              case Nil    => f_in_nnf
              case _ :: _ => skolemizeWith( f_in_nnf, skolem_functions, true )
            }

            val f_no_quant = dropQuantifiers( f_skolemized )

            // If there are not lean predicate symbols, use regular DNF transformation
            val subs = lean_preds match {
              case Nil =>
                val f_dnf = toMagicalDNF( f_no_quant )
                matchClauses( f_dnf, lean_clauses ) match {
                  case Some( s ) => s
                  case None      => throw new LeanCoPNoMatchException( "leanCoP parsing: formula " + f_dnf + " and clauses " + lean_clauses + " do not match." )
                }
              case _ :: _ =>
                val f_clausified = toDefinitionalClausalForm( f_no_quant, lean_preds )
                matchClauses( f_clausified, lean_clauses ) match {
                  case Some( s ) => s
                  case None      => throw new LeanCoPNoMatchException( "leanCoP parsing: formula " + f_clausified + " and clauses " + lean_clauses + " do not match." )
                }
            }

            val sublst = lst_int.flatMap( i => clauses_substitutions.get( i ) match {
              case Some( cs ) => cs.map( s => s.compose( subs ) )
              case None       => List()
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
    } | rep( comment ) ^^ { case _ => None } // No TPTP proof

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
    case formulas => FOLAnd( formulas )
  }

  lazy val formula: PackratParser[FOLFormula] = dbl_impl

  lazy val dbl_impl: PackratParser[FOLFormula] = (
    impl ~ "<=>" ~ dbl_impl ^^ {
      case f1 ~ _ ~ f2 =>
        FOLAnd( FOLOr( FOLNeg( f1 ), f2 ), FOLOr( f1, FOLNeg( f2 ) ) )
    }
    | impl )

  lazy val impl: PackratParser[FOLFormula] = (
    and ~ "=>" ~ impl ^^ { case f1 ~ _ ~ f2 => FOLOr( FOLNeg( f1 ), f2 ) }
    | and )

  lazy val and: PackratParser[FOLFormula] = (
    or ~ "&" ~ and ^^ { case f1 ~ _ ~ f2 => FOLAnd( f1, f2 ) }
    | or )

  lazy val or: PackratParser[FOLFormula] = (
    neg ~ "|" ~ or ^^ { case f1 ~ _ ~ f2 => FOLOr( f1, f2 ) }
    | neg )

  lazy val neg: PackratParser[FOLFormula] = (
    ( "-" | "~" ) ~> neg ^^ { case f => FOLNeg( f ) }
    | quantified )

  lazy val quantified: PackratParser[FOLFormula] = (
    "!" ~ "[" ~> repsep( variable, "," ) ~ "] : " ~ quantified ^^ {
      case vars ~ _ ~ form =>
        vars.foldLeft( form )( ( f, v ) => FOLAllVar( v, f ) )
    }
    | "?" ~ "[" ~> repsep( variable, "," ) ~ "] : " ~ quantified ^^ {
      case vars ~ _ ~ form =>
        vars.foldLeft( form )( ( f, v ) => FOLExVar( v, f ) )
    }
    | neg | atom )

  lazy val atom: PackratParser[FOLFormula] = not_eq | eq | real_atom | lean_atom | quantified | "(" ~> formula <~ ")"
  // These are introduced by leanCoP's (restricted) definitional clausal form translation
  lazy val lean_atom: PackratParser[FOLFormula] = lean_var ^^ {
    case ( i, terms ) =>
      FOLAtom( "leanP" + i, terms )
  }
  lazy val real_atom: PackratParser[FOLFormula] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ {
    case pred ~ _ ~ args => FOLAtom( pred, args )
  }
  lazy val eq: PackratParser[FOLFormula] = term ~ "=" ~ term ^^ {
    case t1 ~ _ ~ t2 => FOLAtom( "=", List( t1, t2 ) )
  }
  lazy val not_eq: PackratParser[FOLFormula] = "(!" ~> term ~ ")" ~ "=" ~ term ^^ {
    case t1 ~ _ ~ _ ~ t2 => FOLNeg( FOLAtom( "=", List( t1, t2 ) ) )
  }

  def term: Parser[FOLTerm] = variable | function | constant | skolem_term
  def function: Parser[FOLTerm] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ { case f ~ _ ~ args => FOLFunction( f, args ) }
  def constant: Parser[FOLConst] = name ^^ { case n => FOLConst( n ) }
  def variable: Parser[FOLVar] = """_[A-Z0-9]+""".r ^^ { case n => FOLVar( n ) }
  def skolem_term: Parser[FOLTerm] = lean_var ^^ {
    case ( i, terms ) =>
      FOLFunction( "leanSk" + i, terms )
  }
  def lean_var: Parser[( Int, List[FOLTerm] )] = """\d+""".r ~ "^" ~ "[" ~ repsep( term, "," ) ~ "]" ^^ {
    case i ~ _ ~ _ ~ terms ~ _ => ( i.toInt, terms )
  }

  def name: Parser[String] = """^(?![_ \d])[^ ():,!?\[\]\-&|=>~]+""".r ^^ { case s => s }
  def integer: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def comment: Parser[String] = """[%](.*)\n""".r ^^ { case s => "" }
}
