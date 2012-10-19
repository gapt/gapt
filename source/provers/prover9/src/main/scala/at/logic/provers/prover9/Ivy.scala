package at.logic.provers.prover9.ivy

import scala.util.parsing.combinator.{RegexParsers, JavaTokenParsers}
import scala.collection.immutable
import at.logic.provers.prover9.lisp.SExpression
import at.logic.provers.prover9.lisp
import at.logic.language.lambda.typedLambdaCalculus.{App, AppN, LambdaExpression}
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.symbols.{VariableStringSymbol, SymbolA}
import at.logic.language.fol
import at.logic.calculi.resolution.base.{FClause, Clause}
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.occurrences
import at.logic.calculi.lk.base.types.FSequent

/**
 * Implements parsing of ivy format: https://www.cs.unm.edu/~mccune/papers/ivy/ into Ivy's Resolution calculus.
 * TODO: transofrmation to Robinson resolution
 */


/* Constructor object, takes a filename and tries to parse as a lisp_file  */
object IvyParser {

  /*
  case class Position(path:List[Int]) { }

  class Hole[T <: LambdaExpression](val exp : T, val pos : Position) {
    def term_in_hole : T = term_in_hole(exp,pos.path)
    def term_in_hole(exp : T, pos : List[Int]) : T = pos match {
      case Nil => exp
      case p::ps => exp match {
        case AppN(f, args) if ((p>0) && (p <= args.size)  ) => term_in_hole(args(p-1), ps)
      }

    }

  } */

  // the type synoyms should make the parsing functions more readable
  type ProofId = String
  type ProofMap = immutable.Map[ProofId, IvyResolutionProof]


  //decompose the proof object to a list and hand it to parse(exp: List[SExpression], found_steps : ProofMap )
  def parse(exp: SExpression ) : IvyResolutionProof =  exp match {
    case lisp.List(Nil) => throw new Exception("Trying to parse an empty proof!")
    case lisp.List(l) => parse(l, immutable.Map[String, IvyResolutionProof]() ) // extract the list of inferences from exp
    case _ => throw new Exception("Parsing error: The proof object is not a list!")
  }

  /* traverses the list of inference sexpressions and returns an IvyResolution proof - this can then be translated to
   * our resolution calculus (i.e. where instantiation is contained in the substitution) */
  def parse(exp: List[SExpression], found_steps : ProofMap ) : IvyResolutionProof =  exp match {
    case List(last) =>
      val (lastid , found_steps_) = parse_step(last, found_steps);
      found_steps_(lastid)

    case head::tail =>
      val (_ , found_steps_) = parse_step(head, found_steps);
      parse(tail, found_steps_);
    case _ => throw new Exception("Cannot create an object for an empty proof (list of inferences is empty).")
  }

  /* parses an inference step and updates the proof map */
  def parse_step(exp : SExpression, found_steps : ProofMap) : (ProofId, ProofMap) = {
    exp match {
      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("input")::Nil) :: clause :: rest  )  => {
        val fclause = parse_clause(clause, is_ladrstyle_variable)

        val inference = InitialClause(clause,
          Clause(fclause.antecedent map (new FormulaOccurrence(_, Nil, occurrences.factory)) ,
                 fclause.succedent map (new FormulaOccurrence(_, Nil, occurrences.factory))))

        (id, found_steps + ((id, inference)) )
      }

        //TODO: implement rules for flip, resolution, paramodulation
    }
  }


  /* create_ladrstyle_symbol and create_prologstyle_symbol implement the logic for the prover9 and prolog style
   * variable naming convention -- both are possible in prover9;
   * see also http://www.cs.unm.edu/~mccune/mace4/manual/2009-11A/syntax.html
   */
  val ladr_variable_regexp = """^[u-z].*$""".r
  def is_ladrstyle_variable(s:String) = ladr_variable_regexp.findFirstIn(s) match {
      case None => false
      case _ => true
    }


  val prolog_variable_regexp = """^[A-Z].*$""".r
  def is_prologstyle_variable(s: String) = ladr_variable_regexp.findFirstIn(s) match {
      case None => false
      case _ => true
    }


  /* parses a clause sexpression to a fclause -- the structure is (or lit1 (or lit2 .... (or litn-1 litn)...)) */
  def parse_clause(exp:SExpression, is_variable_symbol : String => Boolean) : FSequent = exp match {

    case lisp.List( lisp.Atom("or") :: left :: right :: Nil ) =>
      //fol.Or(parse_clause(left, is_variable_symbol), parse_clause(right, is_variable_symbol)  )
      //val letftclause = parse_clause(left, is_variable_symbol)
      val rightclause = parse_clause(right, is_variable_symbol)
      left match {
        case lisp.List( lisp.Atom("not") :: lisp.List( lisp.Atom(name) :: args) :: Nil ) =>
          FSequent(parse_atom(name, args, is_variable_symbol)::Nil, Nil)
        case lisp.List( lisp.Atom(name) :: args) =>
          FSequent(Nil, parse_atom(name, args, is_variable_symbol)::Nil)
      }


    case lisp.List( lisp.Atom("not") :: lisp.List( lisp.Atom(name) :: args) :: Nil ) =>
      //fol.Neg(parse_clause(formula, is_variable_symbol) )
      FSequent(parse_atom(name, args, is_variable_symbol)::Nil, Nil)

    case lisp.List( lisp.Atom(name) :: args) =>
      FSequent(Nil, parse_atom(name, args, is_variable_symbol)::Nil)


    case _ => throw new Exception("Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object.")
  }

  def parse_atom(name: String, args : List[SExpression],is_variable_symbol : String => Boolean) = {
    if (is_variable_symbol(name)) throw new Exception("Parsing Error: Predicate name "+name+" does not conform to naming conventions.")
    val sym = new ConstantStringSymbol(name)
    val argterms = args map (parse_term(_, is_variable_symbol))

    fol.Atom(sym, argterms)

  }

  def parse_term(ts : SExpression, is_variable_symbol : String => Boolean) : fol.FOLTerm = ts match {
    case lisp.Atom(name) =>
      if (is_variable_symbol(name))
        fol.FOLVar(new VariableStringSymbol(name))
      else
        fol.FOLConst(new ConstantStringSymbol(name))
    case lisp.List(lisp.Atom(name)::args) =>
      if (is_variable_symbol(name)) throw new Exception("Parsing Error: Function name "+name+" does not conform to naming conventions.")
      fol.Function(new ConstantStringSymbol(name), args.map(parse_term(_, is_variable_symbol)) )
    case _ =>
      throw new Exception("Parsing Error: Unexpected expression "+ts+" in parsing of a term.")
  }


}
