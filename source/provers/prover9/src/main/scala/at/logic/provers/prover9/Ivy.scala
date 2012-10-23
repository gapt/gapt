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
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.hol.HOLFormula
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import fol.{FOLVar, FOLTerm}
import java.awt.peer.ListPeer

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
  type Position = List[Int]


  //decompose the proof object to a list and hand it to parse(exp: List[SExpression], found_steps : ProofMap )
  def parse(exp: SExpression ) : IvyResolutionProof =  exp match {
    case lisp.List(Nil) => throw new Exception("Trying to parse an empty proof!")
    case lisp.List(l) => parse(l, immutable.Map[String, IvyResolutionProof]() ) // extract the list of inferences from exp
    case _ => throw new Exception("Parsing error: The proof object is not a list!")
  }

  /* traverses the list of inference sexpressions and returns an IvyResolution proof - this can then be translated to
   * our resolution calculus (i.e. where instantiation is contained in the substitution)
   * note: requires that an if inference a references inference b, then a occurs before b in the list */
  def parse(exp: List[SExpression], found_steps : ProofMap ) : IvyResolutionProof =  {
    val is_variable_symbol : (String => Boolean) = is_ladrstyle_variable
    exp match {
      case List(last) =>
        val (lastid , found_steps_) = parse_step(last, found_steps, is_variable_symbol);
        found_steps_(lastid)

      case head::tail =>
        val (_ , found_steps_) = parse_step(head, found_steps, is_variable_symbol);
        parse(tail, found_steps_);
      case _ => throw new Exception("Cannot create an object for an empty proof (list of inferences is empty).")
    }
  }

  /* parses an inference step and updates the proof map  */
  def parse_step(exp : SExpression, found_steps : ProofMap, is_variable_symbol : String => Boolean) : (ProofId, ProofMap) = {
    exp match {
      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("input")::Nil) :: clause :: _  )  => {
        val fclause = parse_clause(clause, is_variable_symbol)

        val inference = InitialClause(id,clause,
          Clause(fclause.antecedent map (new FormulaOccurrence(_, Nil, occurrences.factory)) ,
                 fclause.succedent map (new FormulaOccurrence(_, Nil, occurrences.factory))))

        (id, found_steps + ((id, inference)) )
      }

      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("instantiate")::lisp.Atom(parent_id):: subst_exp::Nil) :: clause :: rest  )  => {
        val parent_proof = found_steps(parent_id)
        val sub : Substitution[FOLTerm] = parse_substitution(subst_exp, is_variable_symbol)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)

        //val ants  = parent_proof.vertex.antecedent zip (fclause.antecedent)
        //val succs  = parent_proof.vertex.succedent zip (fclause.succedent)

        def connect(ancestors: immutable.Seq[FormulaOccurrence], formulas: immutable.Seq[HOLFormula]) :
        immutable.Seq[FormulaOccurrence] =
          (ancestors zip formulas) map ( (v: (FormulaOccurrence, HOLFormula)) =>
            new FormulaOccurrence(v._2, immutable.List(v._1), occurrences.factory))

        val inference = Instantiate(id,clause, sub,
          Clause(connect(parent_proof.vertex.antecedent, fclause.antecedent),
                 connect(parent_proof.vertex.succedent, fclause.succedent)), parent_proof)

        (id, found_steps + ((id, inference)) )


      }

      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("resolve")::
                         lisp.Atom(parent_id1):: lisp.List(position1) ::
                         lisp.Atom(parent_id2):: lisp.List(position2) :: Nil) ::
                       clause :: rest  )  => {
        val parent_proof1 = found_steps(parent_id1)
        val parent_proof2 = found_steps(parent_id2)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)

        val (occ1, polarity1, _) = get_literal_by_position(parent_proof1.vertex, position1, parent_proof1.clause_exp, is_variable_symbol)
        val (occ2, polarity2, _) = get_literal_by_position(parent_proof2.vertex, position2, parent_proof2.clause_exp, is_variable_symbol)

        require(occ1.formula == occ2.formula, "Resolved formula "+occ1.formula +" must be equal to "+occ2.formula+" !")

        def connect(c1 : Clause, c2 : Clause, conclusion : FSequent) : Clause = {
          conclusion match {
            //process antecedent
            case FSequent(x::xs, ys ) =>
              val pos1 = c1.antecedent indexWhere (_.formula == x)
              if (pos1 >= 0) {
                val focc = new FormulaOccurrence(x, c1.antecedent(pos1).ancestors, c1.antecedent(pos1).factory  )
                val rec = connect(Clause(c1.antecedent.filterNot(_ == c1.antecedent(pos1)), c1.succedent), c2, FSequent(xs,ys))
                Clause(focc :: rec.antecedent.toList, rec.succedent)
              } else {
                val pos2 = c2.antecedent indexWhere (_.formula == x)
                if (pos2 >= 0) {
                  val focc = new FormulaOccurrence(x, c2.antecedent(pos2).ancestors, c2.antecedent(pos2).factory  )
                  val rec = connect(c1, Clause(c2.antecedent.filterNot(_ == c2.antecedent(pos2)), c2.succedent), FSequent(xs,ys))
                  Clause(focc :: rec.antecedent.toList, rec.succedent)
                } else throw new Exception("Error in parsing resolution inference: resolved literal not found!")
              }
            //then succedent
            case FSequent(Nil, y::ys ) =>
              val pos1 = c1.succedent indexWhere (_.formula == y)
              if (pos1 >= 0) {
                val focc = new FormulaOccurrence(y, c1.succedent(pos1).ancestors, c1.succedent(pos1).factory  )
                val rec = connect(Clause(c1.antecedent, c1.succedent.filterNot(_ == c1.succedent(pos1))), c2, FSequent(Nil,ys))
                Clause(rec.antecedent, focc :: rec.succedent.toList)
              } else {
                val pos2 = c2.antecedent indexWhere (_.formula == y)
                if (pos2 >= 0) {
                  val focc = new FormulaOccurrence(y, c2.antecedent(pos2).ancestors, c2.antecedent(pos2).factory  )
                  val rec = connect(c1, Clause(c2.antecedent, c2.succedent.filterNot(_ == c2.succedent(pos2))), FSequent(Nil,ys))
                  Clause(rec.antecedent, focc :: rec.succedent.toList)
                } else throw new Exception("Error in parsing resolution inference: resolved literal not found!")
              }
            //base case
            case FSequent(Nil,Nil) => Clause(Nil,Nil)
            case _ => throw new Exception("Unhandled case in calculation of ancestor relationship during creation of a resolution iference!")
          }
        }

        (polarity1, polarity2) match {
          case (true,false) =>
            val clause1 = Clause(parent_proof1.vertex.antecedent, parent_proof1.vertex.succedent filterNot (_ == occ1) )
            val clause2 = Clause(parent_proof2.vertex.antecedent filterNot (_ == occ2), parent_proof2.vertex.succedent )
            val inference = Resolution(id,clause, occ1, occ2, connect(clause1, clause2, fclause), parent_proof1, parent_proof2)
            (id, found_steps + ((id, inference)) )

          case (false,true) =>
            val clause1 = Clause(parent_proof1.vertex.antecedent filterNot (_ == occ1), parent_proof1.vertex.succedent )
            val clause2 = Clause(parent_proof2.vertex.antecedent, parent_proof2.vertex.succedent filterNot (_ == occ2) )
            val inference = Resolution(id,clause, occ1, occ2, connect(clause1, clause2, fclause), parent_proof1, parent_proof2)
            (id, found_steps + ((id, inference)) )

          case _ =>
            throw new Exception("Error parsing resolution inference: must resolve over a positive and a negative literal!")
        }



      }

      //case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("flip")::Nil) :: clause :: rest  )  =>

        //TODO: implement rules for flip, paramodulation
    }
  }

  //def get_literal_by_position(c:Clause, pos:Position)

  //extracts a literal from a clause - since the clause seperates positive and negative clauses,
  // we also need the original SEXpression to make sense of the position.
  // paramdoulation continues inside the term, so we return the remaining position together with the occurrence
  // the boolean indicates a positive or negative formula
  def get_literal_by_position(c:Clause, pos: List[SExpression],
                              clauseexp : SExpression, is_variable_symbol : String => Boolean )
  : (FormulaOccurrence, Boolean, List[SExpression]) = {
    //first convert the sexpression to a list of formulas, convert the index expression to an index in the list
    val lit_list = parse_clause_(clauseexp, is_variable_symbol)
    val (index, remainder) = get_literal_by_position_(pos, lit_list, 0)
    val withindices = lit_list zip (0 to (lit_list.size -1))

    //since a clause is split into negative and positive literals (with order preserved), we need to map the index from
    //the original list to the index in Clause.positive/Clause.negative
    var index_pos = 0
    var index_neg = 0

    for ( (lit,index) <- withindices.take(index+1)) {
      lit match {
        case fol.Atom(_,_) => index_pos = index_pos +1
        case fol.Neg(fol.Atom(_,_)) => index_neg = index_neg +1
        case _ => throw new Exception("Error in resolving position, parsed clause contains non-literal "+lit)
      }
    }

    lit_list(index) match {
      case fol.Atom(_,_) => (c.positive(index_pos-1), true, remainder)
      case fol.Neg(fol.Atom(_,_)) => (c.negative(index_neg-1), false, remainder)
      case _ => throw new Exception("Error in resolving position, parsed clause contains non-literal "+lit_list(index))
    }

  }

  def get_literal_by_position_(pos:List[SExpression], clauseexp : List[HOLFormula], index : Int) : (Int, List[SExpression]) = {
    clauseexp match {
      case Nil =>
        throw new Exception("Error parsing position in SExpression!")
      case x::xs =>
        pos match {
          case Nil => (index, pos) //TODO:check if this is really correct
          case lisp.Atom("1") :: rest => (index, rest)
          case lisp.Atom("2") :: Nil =>
            (index+1, Nil)
          case lisp.Atom("2") :: rest =>
            get_literal_by_position_(rest, xs, index+1 )
          case lisp.Atom(_) :: rest => //this is a position within a term
            (index+1, pos) //TODO:check if this is really correct
          case _ =>
            throw new Exception("Error parsing position in SExpression!")
        }
    }
  }

  def parse_substitution(exp : SExpression, is_variable_symbol : String => Boolean) : Substitution[FOLTerm] = exp match {
    case lisp.List(list) =>
      Substitution[FOLTerm](parse_substitution_(list, is_variable_symbol))
    case _ => throw new Exception("Error parsing substitution expression "+exp+" (not a list)")
  }

  //Note:substitution are sometimes given as lists of cons and sometimes as two-element list...
  def parse_substitution_(exp : List[SExpression], is_variable_symbol : String => Boolean) : List[(FOLVar, FOLTerm)] = exp match {
    case lisp.List(vexp::texp)::xs =>
      val v = parse_term(vexp, is_variable_symbol)
      val t = parse_term(lisp.List(texp), is_variable_symbol)

      v match {
        case v_ : FOLVar =>
          (v_,t) :: parse_substitution_(xs, is_variable_symbol)
        case _ =>
          throw new Exception("Error parsing substitution expression "+exp+": substiution variable was not parsed as variable!")
      }

    case lisp.Cons(vexp, texp)::xs =>
      val v = parse_term(vexp, is_variable_symbol)
      val t = parse_term(texp, is_variable_symbol)

      v match {
        case v_ : FOLVar =>
         (v_,t) :: parse_substitution_(xs, is_variable_symbol)
        case _ =>
          throw new Exception("Error parsing substitution expression "+exp+": substiution variable was not parsed as variable!")
      }
    case Nil =>
      Nil
    case _ => throw new Exception("Error parsing substitution expression "+exp+" (could not match substitution term!)")
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
  def parse_clause(exp:SExpression, is_variable_symbol : String => Boolean) : FSequent = {
    val clauses = parse_clause_(exp, is_variable_symbol)
    var pos : List[HOLFormula] = Nil
    var neg : List[HOLFormula] = Nil

    for (c <- clauses) {
      c match {
        case fol.Neg(formula) =>
          formula match {
            case fol.Atom(_,_) => neg = formula::neg
            case _ => throw new Exception("Error parsing clause: negative Literal "+formula+" is not an atom!")
          }
        case fol.Atom(_,_) =>
              pos = c :: pos
        case _ =>
          throw new Exception("Error parsing clause: formula "+c+" is not a literal!")
      }
    }

    //the literals were prepended to the list, so we have to reverse them to get the original order
    FSequent(neg.reverse, pos.reverse)
  }

  //directly converts a clause as nested or expression into a list with the literals in the same order
  def parse_clause_(exp:SExpression, is_variable_symbol : String => Boolean) : List[HOLFormula] = exp match {
    case lisp.List( lisp.Atom("or") :: left :: right :: Nil ) =>
      val rightclause = parse_clause_(right, is_variable_symbol)

      left match {
        case lisp.List( lisp.Atom("not") :: lisp.List( lisp.Atom(name) :: args) :: Nil ) =>
          fol.Neg(parse_atom(name, args, is_variable_symbol)) :: rightclause
        case lisp.List( lisp.Atom(name) :: args) =>
          parse_atom(name, args, is_variable_symbol) :: rightclause
        case _ => throw new Exception("Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object.")
      }


    case lisp.List( lisp.Atom("not") :: lisp.List( lisp.Atom(name) :: args) :: Nil ) =>
      //fol.Neg(parse_clause(formula, is_variable_symbol) )
      fol.Neg(parse_atom(name, args, is_variable_symbol)) ::Nil

    case lisp.List( lisp.Atom(name) :: args) =>
      parse_atom(name, args, is_variable_symbol) :: Nil

    //the empty clause is denoted by false
    case lisp.Atom("false") =>
      List()

    case _ => throw new Exception("Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object.")
  }

  def parse_atom(name: String, args : List[SExpression],is_variable_symbol : String => Boolean) = {
    if (is_variable_symbol(name)) throw new Exception("Parsing Error: Predicate name "+name+" does not conform to naming conventions.")
    val sym = new ConstantStringSymbol(name)
    val argterms = args map (parse_term(_, is_variable_symbol))

    fol.Atom(sym, argterms)

  }


  //some names are escaped for ivy, see also  LADR-2009-11A/ladr/ivy.c in the Prover9 source
  val ivy_escape_table = Map[String,String]( ("zero_for_ivy","0"),
                                             ("one_for_ivy","1"),
                                             ("quote_for_ivy","'"),
                                             ("backslash_for_ivy","\\\\"),
                                             ("at_for_ivy","@"),
                                             ("meet_for_ivy","^"))
  def rewrite_name(s:String) : String = if (ivy_escape_table contains s) ivy_escape_table(s) else s

  def parse_term(ts : SExpression, is_variable_symbol : String => Boolean) : fol.FOLTerm = ts match {
    case lisp.Atom(name) =>
      val rname = rewrite_name(name)
      if (is_variable_symbol(rname))
        fol.FOLVar(new VariableStringSymbol(rname))
      else
        fol.FOLConst(new ConstantStringSymbol(rname))
    case lisp.List(lisp.Atom(name)::args) =>
      val rname = rewrite_name(name)
      if (is_variable_symbol(rname)) throw new Exception("Parsing Error: Function name "+rname+" does not conform to naming conventions.")
      fol.Function(new ConstantStringSymbol(rname), args.map(parse_term(_, is_variable_symbol)) )
    case _ =>
      throw new Exception("Parsing Error: Unexpected expression "+ts+" in parsing of a term.")
  }


}
