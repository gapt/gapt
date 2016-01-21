
package at.logic.gapt.formats.ivy

import at.logic.gapt.formats.lisp._
import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

/**
 * Implements parsing of ivy format: https://www.cs.unm.edu/~mccune/papers/ivy/ into Ivy's Resolution calculus.
 */

/* Constructor object, takes a filename and tries to parse as a lisp_file  */
object IvyParser extends Logger {
  override def loggerName = "IvyParserLogger"

  //calls the sexpression parser on the given file and parses it, needs a naming convention
  def apply( fn: String ): IvyResolutionProof =
    parse( SExpressionParser.parseFile( fn ) )

  def parseString( sexpr: String ): IvyResolutionProof =
    parse( SExpressionParser.parseString( sexpr ) )

  def parse( exp: Seq[SExpression] ): IvyResolutionProof = {
    require( exp.length >= 1, "An ivy proof must contain at least one proof object, not " + exp.length + "! " )
    if ( exp.length > 1 ) warn( "WARNING: Ivy proof contains more than one proof, taking the first one." )
    parse( exp( 0 ) )
  }

  // the type synoyms should make the parsing functions more readable
  type ProofId = String
  type Position = List[Int]

  //decompose the proof object to a list and hand it to parse(exp: List[SExpression], found_steps : ProofMap )
  def parse( exp: SExpression ): IvyResolutionProof = exp match {
    case LList()         => throw new Exception( "Trying to parse an empty proof!" )
    case LList( l @ _* ) => parse_steps( l ) // extract the list of inferences from exp
    case _               => throw new Exception( "Parsing error: The proof object is not a list!" )
  }

  /* traverses the list of inference sexpressions and returns an IvyResolution proof - this can then be translated to
   * our resolution calculus (i.e. where instantiation is contained in the substitution)
   * note: requires that an if inference a references inference b, then a occurs before b in the list */
  def parse_steps( exp: Seq[SExpression] ): IvyResolutionProof = {
    var lastStep: IvyResolutionProof = null
    val found_steps = mutable.Map[ProofId, IvyResolutionProof]()

    exp foreach { step =>
      lastStep = parse_step( step, found_steps )
      found_steps( lastStep.id ) = lastStep
    }

    lastStep
  }

  /* parses an inference step and updates the proof map  */
  def parse_step( exp: SExpression, found_steps: ProofId => IvyResolutionProof ): IvyResolutionProof =
    exp match {
      /* ================== Atom ========================== */
      case LFun( id, LFun( "input" ), clause, _* ) =>
        InitialClause( id, clause, parse_clause( clause ) )

      /* ================== Instance ========================== */
      case LFun( id, LFun( "instantiate", LAtom( parent_id ), subst_exp ), clause, _* ) =>
        val parent_proof = found_steps( parent_id )
        val sub: FOLSubstitution = parse_substitution( subst_exp )

        Instantiate( id, clause, sub, parse_clause( clause ), parent_proof )

      /* ================== Resolution ========================== */
      case LFun( id, LFun( "resolve",
        LAtom( parent_id1 ), LList( position1 @ _* ),
        LAtom( parent_id2 ), LList( position2 @ _* ) ), clause, _* ) =>
        val parent_proof1 = found_steps( parent_id1 )
        val parent_proof2 = found_steps( parent_id2 )
        val fclause = parse_clause( clause )

        val ( occ1, _ ) = get_literal_by_position( parent_proof1.conclusion, position1, parent_proof1.clause_exp )
        val ( occ2, _ ) = get_literal_by_position( parent_proof2.conclusion, position2, parent_proof2.clause_exp )

        Resolution( id, clause, occ1, occ2, fclause, parent_proof1, parent_proof2 )

      /* ================== Flip ========================== */
      case LFun( id, LFun( "flip", LAtom( parent_id ), LList( position @ _* ) ), clause, _* ) =>
        val parent_proof = found_steps( parent_id )
        val fclause = parse_clause( clause )
        val ( occ, _ ) = get_literal_by_position( parent_proof.conclusion, position, parent_proof.clause_exp )

        parent_proof.conclusion( occ ) match {
          case Eq( left, right ) =>
            Flip( id, clause, occ, fclause, parent_proof )
        }

      /* ================== Paramodulation ========================== */
      case LFun( id, LFun( "paramod",
        LAtom( modulant_id ), LList( mposition @ _* ),
        LAtom( parent_id ), LList( pposition @ _* )
        ), clause, _* ) =>
        val modulant_proof = found_steps( modulant_id )
        val parent_proof = found_steps( parent_id )
        val fclause = parse_clause( clause )
        val ( mocc, direction ) = get_literal_by_position( modulant_proof.conclusion, mposition, modulant_proof.clause_exp )
        require( direction == List( 1 ) || direction == List( 2 ), "Must indicate if paramod or demod!" )
        val orientation = if ( direction.head == 1 ) true else false //true = paramod (left to right), false = demod (right to left)

        require( mocc.isSuc, "Paramodulated literal must be positive!" )
        val ( pocc, int_position ) = get_literal_by_position( parent_proof.conclusion, pposition, parent_proof.clause_exp )

        modulant_proof.conclusion( mocc ) match {
          case Eq( left: FOLTerm, right: FOLTerm ) =>
            val paraformula = if ( orientation )
              replaceTerm_by_in_at( left, right, parent_proof.conclusion( pocc ), int_position ).asInstanceOf[FOLAtom]
            else
              replaceTerm_by_in_at( right, left, parent_proof.conclusion( pocc ), int_position ).asInstanceOf[FOLAtom]

            Paramodulation( id, clause, int_position, mocc, pocc, paraformula, orientation, fclause, modulant_proof, parent_proof )

        }

      /* ================== Propositional ========================== */
      case LFun( id, LFun( "propositional", LAtom( parent_id ) ), clause, _* ) => {
        val parent_proof = found_steps( parent_id )
        val fclause = parse_clause( clause )

        Propositional( id, clause, fclause, parent_proof )
      }

      // new symbol
      case LFun( id, LFun( "new_symbol", LAtom( parent_id ) ), clause, _* ) =>

        val parent_proof = found_steps( parent_id )
        val fclause = parse_clause( clause )
        require( fclause.antecedent.isEmpty, "Expecting only positive equations in parsing of new_symbol rule " + id )
        require( fclause.succedent.size == 1, "Expecting exactly one positive equation in parsing of new_symbol rule " + id )

        val Eq( l: FOLTerm, r: FOLConst ) = fclause( Suc( 0 ) )

        NewSymbol( id, clause, Suc( 0 ), r, l, fclause, parent_proof )

      case _ => throw new Exception( "Error parsing inference rule in expression " + exp )
    }

  //extracts a literal from a clause - since the clause seperates positive and negative clauses,
  // we also need the original SEXpression to make sense of the position.
  // paramodulation continues inside the term, so we return the remaining position together with the occurrence
  // the boolean indicates a positive or negative formula

  def get_literal_by_position( c: FOLClause, pos: Seq[SExpression],
                               clauseexp: SExpression ): ( SequentIndex, List[Int] ) = {
    val ipos = parse_position( pos )
    val ( iformula, termpos ) = parse_clause_frompos( clauseexp, ipos )
    //Remark: we actually return the first occurrence of the formula, not the one at the position indicated as
    //        it should not make a difference. (if f occurs twice in the clause, it might be derived differently
    //        but we usually don't care for that)
    iformula match {
      case a @ FOLAtom( sym, args ) =>
        ( Suc( c.positive.indexOf( a ) ), termpos )
      case Neg( a @ FOLAtom( sym, args ) ) =>
        ( Ant( c.negative.indexOf( a ) ), termpos )
    }
  }

  //term replacement
  //TODO: refactor replacement for lambda expressions
  def replaceTerm_by_in_at( what: FOLTerm, by: FOLTerm, exp: FOLExpression, pos: List[Int] ): FOLExpression = pos match {
    case p :: ps =>
      exp match {
        case FOLAtom( sym, args ) =>
          require( 1 <= p && p <= args.length, "Error in parsing replacement: invalid argument position in atom!" )
          val ( args1, rterm :: args2 ) = args.splitAt( p - 1 )
          FOLAtom( sym, ( args1 ++ List( replaceTerm_by_in_at( what, by, rterm, ps ).asInstanceOf[FOLTerm] ) ++ args2 ) )
        case FOLFunction( sym, args ) =>
          require( 1 <= p && p <= args.length, "Error in parsing replacement: invalid argument position in function!" )
          val ( args1, rterm :: args2 ) = args.splitAt( p - 1 )
          FOLFunction( sym, ( args1 ++ List( replaceTerm_by_in_at( what, by, rterm, ps ).asInstanceOf[FOLTerm] ) ++ args2 ) )
        case _ => throw new Exception( "Error in parsing replacement: unexpected (sub)term " + exp + " )" )
      }

    case Nil =>
      if ( exp == what ) by else throw new Exception( "Error in parsing replacement: (sub)term " + exp + " is not the expected term " + what )
  }

  def parse_position( l: Seq[SExpression] ): List[Int] = l.toList map { case LAtom( s ) => s.toInt }

  def parse_substitution( exp: SExpression ): FOLSubstitution = exp match {
    case LList( list @ _* ) =>
      FOLSubstitution( parse_substitution_( list ) )
    case _ => throw new Exception( "Error parsing substitution expression " + exp + " (not a list)" )
  }

  //Note:substitution are sometimes given as lists of cons and sometimes as two-element list...
  def parse_substitution_( exp: Seq[SExpression] ): List[( FOLVar, FOLTerm )] = exp.toList map {
    case LList( vexp, texp @ _* ) =>
      val v = parse_term( vexp )
      val t = parse_term( LList( texp: _* ) )

      v.asInstanceOf[FOLVar] -> t
    case LCons( vexp, texp ) =>
      val v = parse_term( vexp )
      val t = parse_term( texp )

      v.asInstanceOf[FOLVar] -> t
  }

  /* parses a clause sexpression to a fclause -- the structure is (or lit1 (or lit2 .... (or litn-1 litn)...)) */
  def parse_clause( exp: SExpression ): FOLClause = {
    val clauses = parse_clause_( exp )
    var pos: List[FOLAtom] = Nil
    var neg: List[FOLAtom] = Nil

    for ( c <- clauses ) {
      c match {
        case Neg( formula ) =>
          formula match {
            case a @ FOLAtom( _, _ ) => neg = a :: neg
            case _                   => throw new Exception( "Error parsing clause: negative Literal " + formula + " is not an atom!" )
          }
        case a @ FOLAtom( _, _ ) =>
          pos = a :: pos
        case _ =>
          throw new Exception( "Error parsing clause: formula " + c + " is not a literal!" )
      }
    }

    //the literals were prepended to the list, so we have to reverse them to get the original order
    Sequent( neg.reverse, pos.reverse )
  }

  //TODO: merge code with parse_clause_
  def parse_clause_frompos( exp: SExpression, pos: List[Int] ): ( HOLFormula, List[Int] ) = exp match {
    case LFun( "or", left, right ) =>
      pos match {
        case 1 :: rest =>
          left match {
            case LFun( "not", LFun( name, args @ _* ) ) =>
              val npos = if ( rest.isEmpty ) rest else rest.tail //if we point to a term we have to strip the indicator for neg
              ( Neg( parse_atom( name, args ) ), npos )
            case LFun( name, args @ _* ) =>
              ( parse_atom( name, args ), rest )
            case _ => throw new Exception( "Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object." )
          }
        case 2 :: rest =>
          parse_clause_frompos( right, rest )
        case _ => throw new Exception( "pos " + pos + " did not point to a literal!" )
      }

    case LFun( "not", LFun( name, args @ _* ) ) =>
      val npos = if ( pos.isEmpty ) pos else pos.tail //if we point to a term we have to strip the indicator for neg
      ( Neg( parse_atom( name, args ) ), npos )

    case LFun( name, args @ _* ) =>
      ( parse_atom( name, args ), pos )

    //the empty clause is denoted by false
    case LAtom( "false" ) =>
      throw new Exception( "Parsing Error: want to extract literal from empty clause!" )

    case _ => throw new Exception( "Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object." )
  }

  //directly converts a clause as nested or expression into a list with the literals in the same order
  def parse_clause_( exp: SExpression ): List[HOLFormula] = exp match {
    case LFun( "or", left, right ) =>
      val rightclause = parse_clause_( right )

      left match {
        case LFun( "not", LFun( name, args @ _* ) ) =>
          Neg( parse_atom( name, args ) ) :: rightclause
        case LFun( name, args @ _* ) =>
          parse_atom( name, args ) :: rightclause
        case _ => throw new Exception( "Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object." )
      }

    case LFun( "not", LFun( name, args @ _* ) ) =>
      Neg( parse_atom( name, args ) ) :: Nil

    case LFun( name, args @ _* ) =>
      parse_atom( name, args ) :: Nil

    //the empty clause is denoted by false
    case LAtom( "false" ) =>
      List()

    case _ => throw new Exception( "Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object." )
  }

  def parse_atom( name: String, args: Seq[SExpression] ) = {
    val argterms = args map parse_term
    if ( name == "=" ) {
      require( args.length == 2, "Error parsing equality: = must be a binary predicate!" )
      Eq( argterms( 0 ), argterms( 1 ) )
    } else {
      FOLAtom( name, argterms )
    }

  }

  //some names are escaped for ivy, see also  LADR-2009-11A/ladr/ivy.c in the Prover9 source
  val ivy_escape_table = Map[String, String](
    ( "zero_for_ivy", "0" ),
    ( "one_for_ivy", "1" ),
    ( "quote_for_ivy", "'" ),
    ( "backslash_for_ivy", "\\\\" ),
    ( "at_for_ivy", "@" ),
    ( "meet_for_ivy", "^" )
  )
  def rewrite_name( s: String ): String = if ( ivy_escape_table contains s ) ivy_escape_table( s ) else s

  def parse_term( ts: SExpression ): FOLTerm = ts match {
    case LAtom( name ) =>
      val rname = rewrite_name( name )
      FOLVar( rname )
    case LFun( name, args @ _* ) =>
      val rname = rewrite_name( name )
      FOLFunction( rname, args.map( parse_term( _ ) ) )
    case _ =>
      throw new Exception( "Parsing Error: Unexpected expression " + ts + " in parsing of a term." )
  }

}
