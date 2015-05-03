package at.logic.gapt.formats.leanCoP

import at.logic.gapt.language.fol._
import at.logic.gapt.expr._
import at.logic.gapt.language.fol.algorithms.FOLMatchingAlgorithm
import at.logic.gapt.proofs.expansionTrees.{ ExpansionTree, ExpansionSequent, formulaToExpansionTree }

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

  // Restricted definitional clausal form (implemented by leanCoP)
  // Takes a formula in NNF and returns a list of clauses in DNF (possibly with
  // introduced definitions)
  // (reverse engineering leanCoP)
  def toDefinitionalClausalForm( f: FOLFormula ): FOLFormula = {
    var i = 0

    def toDCF( f: FOLFormula, inConj: Boolean ): ( FOLFormula, List[FOLFormula] ) = f match {
      case FOLAtom( _, _ )        => ( f, List() )
      case Neg( FOLAtom( _, _ ) ) => ( f, List() )
      case And( f1, f2 ) =>
        val ( f1d, d1 ) = toDCF( f1, true )
        val ( f2d, d2 ) = toDCF( f2, true )
        ( And( f1d, f2d ), d1 ++ d2 )
      case Or( f1, f2 ) => {
        if ( inConj ) {
          val ( f1d, d1 ) = toDCF( f1, inConj )
          val ( f2d, d2 ) = toDCF( f2, inConj )
          val vars = freeVariables( f )
          val new_pred = FOLAtom( "leanP" + i, vars )
          i += 1
          val def1 = And( Neg( new_pred ), f1d )
          val def2 = And( Neg( new_pred ), f2d )
          ( new_pred, def1 :: def2 :: d1 ++ d2 )
        } else {
          val ( f1d, d1 ) = toDCF( f1, inConj )
          val ( f2d, d2 ) = toDCF( f2, inConj )
          ( Or( f1d, f2d ), d1 ++ d2 )
        }
      }
      case _ => throw new Exception( "Unsuported format for definitional clausal transformation." )
    }

    // to DNF
    def toClause( f: FOLFormula ): List[FOLFormula] = f match {
      case FOLAtom( _, _ )         => List( f )
      case Neg( FOLAtom( _, _ ) )  => List( f )
      case Or( f1, f2 )            => toClause( f1 ) ++ toClause( f2 )
      case And( f1, Or( f2, f3 ) ) => toClause( And( f1, f2 ) ) ++ toClause( And( f1, f3 ) )
      case And( Or( f1, f2 ), f3 ) => toClause( And( f1, f3 ) ) ++ toClause( And( f2, f3 ) )
      case And( f1, f2 )           => List( f )
      case _                       => throw new Exception( "ERROR: Unexpected case while distributing Ors over Ands." )
    }

    val ( fd, defs ) = toDCF( f, false )

    Or( fd :: defs.flatMap( d => toClause( d ) ) )
  }

  // Trusting that there is no variable capture.
  def dropQuantifiers( f: FOLFormula ): FOLFormula = f match {
    case FOLAtom( _, _ ) => f
    case Neg( f1 )       => Neg( dropQuantifiers( f1 ) )
    case Imp( f1, f2 )   => Imp( dropQuantifiers( f1 ), dropQuantifiers( f2 ) )
    case And( f1, f2 )   => And( dropQuantifiers( f1 ), dropQuantifiers( f2 ) )
    case Or( f1, f2 )    => Or( dropQuantifiers( f1 ), dropQuantifiers( f2 ) )
    case Ex( x, f1 )     => dropQuantifiers( f1 )
    case All( x, f1 )    => dropQuantifiers( f1 )
  }

  def expansionSequent: Parser[ExpansionSequent] =
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
            val formula = input_formulas( name )._1 // FOLFormula
            val negated_axiom = {
              if ( input_formulas( name )._2 == "axiom" ) toNNF( Neg( formula ) )
              else formula
            }
            val clausified = toDefinitionalClausalForm( dropQuantifiers( negated_axiom ) )
            val lean_clauses = Or( lst_int.map( i => clauses( i )._1 ).toList )
            val subs = FOLMatchingAlgorithm.matchTerms( clausified, lean_clauses ) match {
              case Some( s ) => s
              case None      => throw new Exception( "leanCoP parsing: formulas " + clausified + " and " + lean_clauses + "do not match." )
            }
            val sublst = lst_int.flatMap( i => clauses_substitutions.get( i ) match {
              case Some( cs ) => cs.map( s => s.compose( subs ) )
              case None       => List()
            } ).toList
            map + ( name -> ( ( formula, sublst ) ) )
        }

        val ( ant, succ ) = formula_substitutions.foldLeft( ( List[ExpansionTree](), List[ExpansionTree]() ) ) {
          case ( ( a, s ), ( name, ( form, sublst ) ) ) =>
            val pos = if ( input_formulas( name )._2 == "axiom" ) false else true;
            val et = formulaToExpansionTree( form, sublst, pos )
            if ( pos ) ( a, ( et :: s ) )
            else ( ( et :: a ), s )
        }

        new ExpansionSequent( ant, succ )
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

  def clause: Parser[FOLFormula] = "[" ~> repsep( formula, "," ) <~ "]" ^^ {
    case formulas => And( formulas )
  }

  lazy val formula: PackratParser[FOLFormula] = formula_def | ( "(" ~> formula <~ ")" )
  lazy val formula_def: PackratParser[FOLFormula] = neg | and | or | impl | dbl_impl | forall | exists | atom

  def term: Parser[FOLTerm] = variable | function | constant | skolem_term
  def function: Parser[FOLTerm] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ { case f ~ _ ~ args => FOLFunction( f, args ) }
  def constant: Parser[FOLConst] = name ^^ { case n => FOLConst( n ) }
  def variable: Parser[FOLVar] = """_[A-Z0-9]+""".r ^^ { case n => FOLVar( n ) }
  def skolem_term: Parser[FOLTerm] = lean_var ^^ {
    case ( i, terms ) =>
      FOLFunction( "sk" + i, terms )
  }

  lazy val atom: PackratParser[FOLFormula] = real_atom | lean_atom
  // These are introduced by leanCoP's (restricted) definitional clausal form translation
  lazy val lean_atom: PackratParser[FOLFormula] = lean_var ^^ {
    case ( i, terms ) =>
      FOLAtom( "leanP" + i, terms )
  }
  lazy val real_atom: PackratParser[FOLFormula] = name ~ "(" ~ repsep( term, "," ) <~ ")" ^^ { case pred ~ _ ~ args => FOLAtom( pred, args ) }
  lazy val neg: PackratParser[FOLFormula] = "-" ~> formula ^^ { case f => Neg( f ) }
  lazy val and: PackratParser[FOLFormula] = formula ~ "&" ~ formula ^^ { case f1 ~ _ ~ f2 => And( f1, f2 ) }
  lazy val or: PackratParser[FOLFormula] = formula ~ "|" ~ formula ^^ { case f1 ~ _ ~ f2 => Or( f1, f2 ) }
  lazy val impl: PackratParser[FOLFormula] = formula ~ "=>" ~ formula ^^ { case f1 ~ _ ~ f2 => Imp( f1, f2 ) }
  lazy val dbl_impl: PackratParser[FOLFormula] = formula ~ "<=>" ~ formula ^^ { case f1 ~ _ ~ f2 => And( Imp( f1, f2 ), Imp( f2, f1 ) ) }
  lazy val forall: PackratParser[FOLFormula] = "!" ~ "[" ~> variable ~ "] :" ~ formula ^^ { case v ~ _ ~ f => All( v, f ) }
  lazy val exists: PackratParser[FOLFormula] = "?" ~ "[" ~> variable ~ "] :" ~ formula ^^ { case v ~ _ ~ f => Ex( v, f ) }

  def name: Parser[String] = """^(?!_)[^ ():,!?\[\]\-&|=>]+""".r ^^ { case s => s }
  def integer: Parser[Int] = """\d+""".r ^^ { _.toInt }
  def lean_var: Parser[( Int, List[FOLTerm] )] = """\d+""".r ~ "^" ~ "[" ~ repsep( term, "," ) ~ "]" ^^ {
    case i ~ _ ~ _ ~ terms ~ _ => ( i.toInt, terms )
  }

  def comment: Parser[String] = """[%](.*)\n""".r ^^ { case s => "" }
}
