package at.logic.provers.prover9.ivy

import scala.collection.immutable
import at.logic.provers.prover9.lisp
import at.logic.provers.prover9.lisp.{SExpressionParser, SExpression}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.{EqSymbol, ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.symbols.{VariableStringSymbol, SymbolA}
import at.logic.language.fol
import at.logic.calculi.resolution.base.{FClause, Clause}
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.occurrences
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.hol.HOLFormula
import fol._
import at.logic.algorithms.rewriting.TermReplacement
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol

/**
 * Implements parsing of ivy format: https://www.cs.unm.edu/~mccune/papers/ivy/ into Ivy's Resolution calculus.
 * TODO: transofrmation to Robinson resolution
 */


/* Constructor object, takes a filename and tries to parse as a lisp_file  */
object IvyParser {
  //easy parametrization to choose naming conventions (there is no information about this in the ivy format)
  sealed abstract class VariableNamingConvention;
  case object PrologStyleVariables extends VariableNamingConvention;
  case object LadrStyleVariables extends VariableNamingConvention;
  case object IvyStyleVariables extends VariableNamingConvention;

  //calls the sexpression parser on the given file and parses it, needs a naming convention
  def apply(fn : String, naming_convention : VariableNamingConvention) : IvyResolutionProof = {
    naming_convention match {
      case PrologStyleVariables => apply_(fn, is_prologstyle_variable)
      case LadrStyleVariables => apply_(fn, is_ladrstyle_variable)
      case IvyStyleVariables => apply_(fn, is_ivy_variable)
    }
  }

  //calls the sexpression parser on the given file and parses it, needs a naming convention
  def apply_(fn : String, is_variable_symbol : (String => Boolean) ): IvyResolutionProof = {
    val exp = SExpressionParser(fn)
    require(exp.length >= 1, "An ivy proof must contain at least one proof object, not "+exp.length+"! "+exp)
    if (exp.length >1) println("WARNING: Ivy proof in "+fn+" contains more than one proof, taking the first one.")
    parse(exp(0), is_variable_symbol)
  }

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

  var debug : Boolean = true
  private def debug(a:Any) : Unit = if (debug) { println("Debug: "+a.toString) }

  // the type synoyms should make the parsing functions more readable
  type ProofId = String
  type ProofMap = immutable.Map[ProofId, IvyResolutionProof]
  type Position = List[Int]


  //decompose the proof object to a list and hand it to parse(exp: List[SExpression], found_steps : ProofMap )
  def parse(exp: SExpression, is_variable_symbol : (String => Boolean) ) : IvyResolutionProof =  exp match {
    case lisp.List(Nil) => throw new Exception("Trying to parse an empty proof!")
    case lisp.List(l) => parse(l, immutable.Map[String, IvyResolutionProof](), is_variable_symbol ) // extract the list of inferences from exp
    case _ => throw new Exception("Parsing error: The proof object is not a list!")
  }

  /* traverses the list of inference sexpressions and returns an IvyResolution proof - this can then be translated to
   * our resolution calculus (i.e. where instantiation is contained in the substitution)
   * note: requires that an if inference a references inference b, then a occurs before b in the list */
  def parse(exp: List[SExpression], found_steps : ProofMap, is_variable_symbol : String => Boolean )
    : IvyResolutionProof =  {
    exp match {
      case List(last) =>
        val (lastid , found_steps_) = parse_step(last, found_steps, is_variable_symbol);
        found_steps_(lastid)

      case head::tail =>
        val (_ , found_steps_) = parse_step(head, found_steps, is_variable_symbol);
        parse(tail, found_steps_, is_variable_symbol);
      case _ => throw new Exception("Cannot create an object for an empty proof (list of inferences is empty).")
    }
  }

  /* parses an inference step and updates the proof map  */
  def parse_step(exp : SExpression, found_steps : ProofMap, is_variable_symbol : String => Boolean) : (ProofId, ProofMap) = {
    exp match {
      case lisp.List(lisp.Atom(id) :: _) => debug("processing inference "+id)
      case _ => ()
    }
    exp match {
      /* ================== Atom ========================== */
      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("input")::Nil) :: clause :: _  )  => {
        val fclause = parse_clause(clause, is_variable_symbol)

        val inference = InitialClause(id,clause,
          Clause(fclause.antecedent map (occurrences.factory.createFormulaOccurrence(_, Nil)) ,
                 fclause.succedent map (occurrences.factory.createFormulaOccurrence(_, Nil))))

        require(inference.root.toFSequent setEquals fclause, "Error in Atom parsing: required result="+fclause+" but got: "+inference.root)
        (id, found_steps + ((id, inference)) )
      }

      /* ================== Instance ========================== */
      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("instantiate")::lisp.Atom(parent_id):: subst_exp::Nil) :: clause :: rest  )  => {
        val parent_proof = found_steps(parent_id)
        val sub : Substitution[FOLTerm] = parse_substitution(subst_exp, is_variable_symbol)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)

        def connect(ancestors: immutable.Seq[FormulaOccurrence], formulas: immutable.Seq[HOLFormula]) :
        immutable.Seq[FormulaOccurrence] =
          (ancestors zip formulas) map ( (v: (FormulaOccurrence, HOLFormula)) =>
            occurrences.factory.createFormulaOccurrence(v._2, immutable.List(v._1)))

        val inference = Instantiate(id,clause, sub,
          Clause(connect(parent_proof.vertex.antecedent, fclause.antecedent),
                 connect(parent_proof.vertex.succedent, fclause.succedent)), parent_proof)

        require(inference.root.toFSequent setEquals fclause, "Error in Instance parsing: required result="+fclause+" but got: "+inference.root)
        (id, found_steps + ((id, inference)) )


      }

      /* ================== Resolution ========================== */
      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("resolve")::
                         lisp.Atom(parent_id1):: lisp.List(position1) ::
                         lisp.Atom(parent_id2):: lisp.List(position2) :: Nil) ::
                       clause :: rest  )  => {
        val parent_proof1 = found_steps(parent_id1)
        val parent_proof2 = found_steps(parent_id2)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)

        try {
        val (occ1, polarity1, _) = get_literal_by_position(parent_proof1.vertex, position1, parent_proof1.clause_exp, is_variable_symbol)
        val (occ2, polarity2, _) = get_literal_by_position(parent_proof2.vertex, position2, parent_proof2.clause_exp, is_variable_symbol)

        require(occ1.formula == occ2.formula, "Resolved formula "+occ1.formula +" must be equal to "+occ2.formula+" !")

        def connect(c1 : Clause, c2 : Clause, conclusion : FSequent) : Clause = {
          conclusion match {
            //process antecedent
            case FSequent(x::xs, ys ) =>
              val pos1 = c1.antecedent indexWhere (_.formula == x)
              if (pos1 >= 0) {
                val focc = c1.antecedent(pos1).factory.createFormulaOccurrence(x, c1.antecedent(pos1).ancestors  )
                val rec = connect(Clause(c1.antecedent.filterNot(_ == c1.antecedent(pos1)), c1.succedent), c2, FSequent(xs,ys))
                Clause(focc :: rec.antecedent.toList, rec.succedent)
              } else {
                val pos2 = c2.antecedent indexWhere (_.formula == x)
                if (pos2 >= 0) {
                  val focc =  c2.antecedent(pos2).factory.createFormulaOccurrence(x, c2.antecedent(pos2).ancestors )
                  val rec = connect(c1, Clause(c2.antecedent.filterNot(_ == c2.antecedent(pos2)), c2.succedent), FSequent(xs,ys))
                  Clause(focc :: rec.antecedent.toList, rec.succedent)
                } else throw new Exception("Error in parsing resolution inference: resolved literal "+x+" not found!")
              }
            //then succedent
            case FSequent(Nil, y::ys ) =>
              val pos1 = c1.succedent indexWhere (_.formula == y)
              if (pos1 >= 0) {
                val focc = c1.succedent(pos1).factory.createFormulaOccurrence(y, c1.succedent(pos1).ancestors )
                val rec = connect(Clause(c1.antecedent, c1.succedent.filterNot(_ == c1.succedent(pos1))), c2, FSequent(Nil,ys))
                Clause(rec.antecedent, focc :: rec.succedent.toList)
              } else {
                val pos2 = c2.succedent indexWhere (_.formula == y)
                if (pos2 >= 0) {
                  val focc = c2.succedent(pos2).factory.createFormulaOccurrence(y, c2.succedent(pos2).ancestors  )
                  val rec = connect(c1, Clause(c2.antecedent, c2.succedent.filterNot(_ == c2.succedent(pos2))), FSequent(Nil,ys))
                  Clause(rec.antecedent, focc :: rec.succedent.toList)
                } else throw new Exception("Error in parsing resolution inference: resolved literal "+y+" not found!")
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

            require(inference.root.toFSequent setEquals fclause, "Error in Resolution parsing: required result="+fclause+" but got: "+inference.root)
            (id, found_steps + ((id, inference)) )

          case (false,true) =>
            val clause1 = Clause(parent_proof1.vertex.antecedent filterNot (_ == occ1), parent_proof1.vertex.succedent )
            val clause2 = Clause(parent_proof2.vertex.antecedent, parent_proof2.vertex.succedent filterNot (_ == occ2) )
            val inference = Resolution(id,clause, occ1, occ2, connect(clause1, clause2, fclause), parent_proof1, parent_proof2)

            require(inference.root.toFSequent setEquals fclause, "Error in Resolution parsing: required result="+fclause+" but got: "+inference.root)
            (id, found_steps + ((id, inference)) )

          case _ =>
            throw new Exception("Error parsing resolution inference: must resolve over a positive and a negative literal!")
        }

        } catch {
          case e : Exception =>
            debug("Exception in id "+id)
            debug(parent_proof1)
            debug(parent_proof2)
            debug(position1)
            debug(position2)
          throw e
        }

      }

      /* ================== Flip ========================== */
      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("flip")::lisp.Atom(parent_id)::lisp.List(position)::Nil) :: clause :: rest  )  =>
        val parent_proof = found_steps(parent_id)
        val fclause = parse_clause(clause, is_variable_symbol)
        val (occ, polarity, _) = get_literal_by_position(parent_proof.root, position, parent_proof.clause_exp, is_variable_symbol)
        //require(polarity == true, "Flipped literals must be positive!"+parent_proof.clause_exp+" -> "+clause)

        occ.formula match {
          case fol.Equation(left,right) =>
            //the negative literals are the same
            def connect_directly(x:FormulaOccurrence) = x.factory.createFormulaOccurrence(x.formula, x::Nil)

            polarity match {
              case true =>
                val neglits = parent_proof.root.negative map connect_directly
                val (pos1, pos2) = parent_proof.root.positive.splitAt( parent_proof.root.positive.indexOf(occ))
                val (pos1_, pos2_) = (pos1 map connect_directly, pos2 map  connect_directly)
                val flipped = occ.factory.createFormulaOccurrence(fol.Equation(right, left), occ::Nil)
                val inference = Flip(id, clause, flipped, Clause(neglits, pos1_ ++ List(flipped) ++ pos2_.tail ), parent_proof)
                require(fclause setEquals inference.root.toFSequent,
                  "Error parsing flip rule: inferred clause "+inference.root.toFSequent +
                    " is not the same as given clause "+ fclause)
                //println("new Flip rule: "+id+ " : "+inference)
                (id, found_steps + ((id, inference)))

              case false =>
                val poslits = parent_proof.root.positive map connect_directly
                val (neg1, neg2) = parent_proof.root.negative.splitAt( parent_proof.root.negative.indexOf(occ))
                val (neg1_, neg2_) = (neg1 map connect_directly, neg2 map  connect_directly)
                val flipped = occ.factory.createFormulaOccurrence(fol.Equation(right, left), occ::Nil)
                val inference = Flip(id, clause, flipped, Clause(neg1_ ++ List(flipped) ++ neg2_.tail, poslits ), parent_proof)
                require(fclause setEquals inference.root.toFSequent,
                  "Error parsing flip rule: inferred clause "+inference.root.toFSequent +
                    " is not the same as given clause "+ fclause)
                //println("new Flip rule: "+id+ " : "+inference)
                (id, found_steps + ((id, inference)))
            }

          case _ =>
            throw new Exception("Error parsing position in flip rule: literal "+occ.formula+" is not the equality predicate.")

        }

      /* ================== Paramodulation ========================== */
      case lisp.List( lisp.Atom(id)::
                      lisp.List(lisp.Atom("paramod")::lisp.Atom(modulant_id)::lisp.List(mposition)::
                                                      lisp.Atom(parent_id)::  lisp.List(pposition):: Nil) ::
                      clause :: rest  )  =>
        val modulant_proof = found_steps(modulant_id)
        val parent_proof = found_steps(parent_id)
        val fclause = parse_clause(clause, is_variable_symbol)
        val (mocc, mpolarity, _) = get_literal_by_position(modulant_proof.root, mposition, modulant_proof.clause_exp, is_variable_symbol)
        debug("found occurrence of equation: "+mocc+" at pos "+mposition)
        require(mpolarity == true, "Paramodulated literal must be positive!")
        val (pocc, polarity, int_position) = get_literal_by_position(parent_proof.root, pposition, parent_proof.clause_exp, is_variable_symbol)
        debug("found occurrence of target formula:"+pocc+" at pos "+pposition)

        mocc.formula match {
          case fol.Equation(left,right) =>
            def connect_directly(x:FormulaOccurrence) = x.factory.createFormulaOccurrence(x.formula, x::Nil)
            debug(polarity)
            polarity match {
              case true =>
                val neglits = parent_proof.root.negative map connect_directly
                val (pneg, ppos ) = (modulant_proof.root.negative map connect_directly, modulant_proof.root.positive.filterNot(_ == mocc) map connect_directly)
                val (pos1, pos2) = parent_proof.root.positive.splitAt( parent_proof.root.positive.indexOf(pocc))
                val (pos1_, pos2_) = (pos1 map connect_directly, pos2 map  connect_directly)

                debug("remaining position: "+int_position+ " full position "+pposition)
                debug("replace: "+left+" by "+right+" in "+pocc.formula)
                val paraformula = replaceTerm_by_in_at(left, right, pocc.formula.asInstanceOf[FOLFormula], int_position ).asInstanceOf[FOLFormula]
                val para = pocc.factory.createFormulaOccurrence(paraformula,  mocc::pocc::Nil)
                /*debug("Context is:" +ppos)
                debug("Context is:" +pos1_)
                debug("Context is:" +pos2_)
                debug("Together:"+ (ppos ++ pos1_  ++ pos2_.tail)) */

                val inferred_clause = Clause(pneg ++ neglits, ppos ++ pos1_ ++ List(para) ++ pos2_.tail)
                debug("inferred clause: " + inferred_clause)

                val inference = Paramodulation(id, clause, int_position, para, inferred_clause, modulant_proof, parent_proof)
                debug("paramod root:    "+ inference.root)
                require(inference.root.toFSequent setEquals fclause, "Error in Paramodulation parsing: required result="+fclause+" but got: "+inference.root)

                //debug("new Paramod rule: "+id+ " : "+inference)
                (id, found_steps + ((id, inference)))

              case false =>
                val poslits = parent_proof.root.positive map connect_directly
                val (pneg, ppos ) = (modulant_proof.root.negative map connect_directly, modulant_proof.root.positive.filterNot(_ == mocc) map connect_directly)
                val (neg1, neg2) = parent_proof.root.negative.splitAt( parent_proof.root.negative.indexOf(pocc))
                val (neg1_, neg2_) = (neg1 map connect_directly, neg2 map  connect_directly)

                debug("remaining position: "+int_position+ " full position "+pposition)
                debug("replace: "+left+" by "+right+" in "+pocc.formula)
                val paraformula = replaceTerm_by_in_at(left, right, pocc.formula.asInstanceOf[FOLFormula], int_position ).asInstanceOf[FOLFormula]
                val para = pocc.factory.createFormulaOccurrence(paraformula,  mocc::pocc::Nil)
                val inferred_clause = Clause(pneg ++ neg1_ ++ List(para) ++ neg2_.tail, ppos ++ poslits)

                val inference = Paramodulation(id, clause, int_position, para, inferred_clause, modulant_proof, parent_proof)

                require(inference.root.toFSequent setEquals fclause, "Error in Paramodulation parsing: required result="+fclause+" but got: "+inference.root)
                //debug("new Paramod rule: "+id+ " : "+inference)
                (id, found_steps + ((id, inference)))
            }


          case _ =>
            throw new Exception("Error parsing position in paramod rule: literal "+mocc.formula+" is not the equality predicate.")

        }

      /* ================== Propositional ========================== */
      case lisp.List( lisp.Atom(id):: lisp.List(lisp.Atom("propositional")::lisp.Atom(parent_id)::Nil) :: clause :: rest  )  => {
        val parent_proof = found_steps(parent_id)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)

        def list_withoutn[A](l : List[A], n:Int) : List[A] = l match {
          case x::xs =>
            if (n==0) xs else x::list_withoutn(xs,n-1)
          case Nil => Nil
        }

        //connects ancestors to formulas
        def connect(ancestors: immutable.List[FormulaOccurrence], formulas: immutable.List[HOLFormula]) :
          List[FormulaOccurrence] = {
          //find ancestor for every formula in conclusion clause
          debug("connecting "+formulas+" to ancestors "+ancestors)
          val (occs, rem) = connect_(ancestors, formulas)
          debug("connected  "+occs+" remaining: "+rem)
          //now connect the contracted formulas
          val connected : List[FormulaOccurrence] = connect_missing(occs, rem)
          debug("connected2 "+connected)
          connected
        }

        //connects each formula to an ancestor, returns a pair of connected formulas and unconnected ancestors
        def connect_(ancestors: immutable.List[FormulaOccurrence], formulas: immutable.List[HOLFormula]) :
            (immutable.List[FormulaOccurrence], immutable.List[FormulaOccurrence]) = {
          formulas match {
            case x::xs =>
              val index = ancestors.indexWhere(_.formula == x)
              require(index >= 0, "Error connecting ancestors in propositional ivy inference: formula "+x+" does not occur in ancestors "+ancestors)
              val anc = ancestors(index)
              val occ = anc.factory.createFormulaOccurrence(x, anc::Nil  )
              val (occs, rem) = connect_(list_withoutn(ancestors, index), xs)

              (occ :: occs, rem)

            case Nil => (Nil, ancestors)
          }
        }

        //connects unconnected (missing) ancestors to list of potential targets, returns list of updated targets
        def connect_missing(targets : immutable.List[FormulaOccurrence], missing : immutable.List[FormulaOccurrence])
           : immutable.List[FormulaOccurrence] = missing match {
          case x::xs =>
            debug("trying to append "+x+" to possibilities "+targets)
            val targets_ = connect_missing_(targets, x)
            connect_missing(targets_, xs)
          case Nil =>
            targets
        }

        //connects one missing occurence to possible tagets, returns list of updated targets
        def connect_missing_(targets : immutable.List[FormulaOccurrence], missing : FormulaOccurrence)
           : immutable.List[FormulaOccurrence] = targets match {
          case x::xs =>
            if (missing.formula == x.formula)
              immutable.List(x.factory.createFormulaOccurrence(x.formula, immutable.List(missing) ++ x.ancestors)) ++ xs
            else
              immutable.List(x) ++ connect_missing_(xs, missing)
          case Nil =>
            throw new Exception("Error connecting factorized literal, no suitable successor found!")
        }

        debug("propositional inference: "+parent_proof)
        val inference = Propositional(id,clause,
          Clause(connect(parent_proof.vertex.antecedent.toList, fclause.antecedent.toList),
            connect(parent_proof.vertex.succedent.toList, fclause.succedent.toList)), parent_proof)

        require(inference.root.toFSequent setEquals fclause, "Error in Propositional parsing: required result="+fclause+" but got: "+inference.root)
        (id, found_steps + ((id, inference)) )


      }

      // new symbol
      case lisp.List( lisp.Atom(id)::
        lisp.List(lisp.Atom("new_symbol")::lisp.Atom(parent_id):: Nil) ::
        clause :: rest  ) =>

        val parent_proof = found_steps(parent_id)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)
        require(fclause.antecedent.isEmpty, "Expecting only positive equations in parsing of new_symbol rule "+id)
        require(fclause.succedent.size == 1, "Expecting exactly one positive equation in parsing of new_symbol rule "+id)
        val Equation(l,r) = fclause.succedent(0)

        def vars(exp : LambdaExpression) : Set[Var] = exp match {
          case Var(_,_) => Set(exp.asInstanceOf[Var])
          case App(s,t) => vars(s) ++ vars(t)
          case Abs(x,t) => vars(t) ++ Set(x)
        }

        val additional_syms = vars(r).diff(vars(l))
        require(additional_syms.size == 1, "" +
          "Expecting exactly one additional symbol in "+l+" in contrast to "+r+"! (rule id="+id+")")

        val constsym = additional_syms.head.asInstanceOf[FOLConst]

        val symvar= FOLVar(VariableStringSymbol(constsym.name.toString))
        val r_ : FOLTerm = TermReplacement[FOLTerm](constsym, symvar, r)
        val matching = FOLMatchingAlgorithm.matchTerm(r_, l, List())

        require(! matching.isEmpty, "Could not match "+r_ +" to "+l+" in parsing of new_symbol rule "+id)

        def connect_with_same_name(parent_occ: FormulaOccurrence, f: FOLFormula) = {
          parent_occ.factory.createFormulaOccurrence(f, parent_occ::Nil)
        }

        val Some(m) = matching
        val nclause = Clause(Nil, connect_with_same_name(parent_proof.root.succedent(0), fclause.succedent(0).asInstanceOf[FOLFormula])::Nil)
        val inference = NewSymbol(id, clause, constsym, m(symvar).asInstanceOf[FOLTerm], nclause, parent_proof)

        (id, found_steps +((id,inference)))

      case _ => throw new Exception("Error parsing inference rule in expression "+exp)
    }
  }

  //extracts a literal from a clause - since the clause seperates positive and negative clauses,
  // we also need the original SEXpression to make sense of the position.
  // paramodulation continues inside the term, so we return the remaining position together with the occurrence
  // the boolean indicates a positive or negative formula

  def get_literal_by_position(c:Clause, pos: List[SExpression],
                              clauseexp : SExpression, is_variable_symbol : String => Boolean )
  : (FormulaOccurrence, Boolean, List[Int]) = {
      val expformulas = parse_clause_(clauseexp, is_variable_symbol)
      val ipos = parse_position(pos)
      val (findex, termpos) = index_at(expformulas, ipos)
      var cpos = 0
      var cneg = 0
      val clause_indices =
        for ( f <- expformulas ) yield f match {
          case fol.Neg(_) => cneg = cneg +1; cneg
          case _ => cpos = cpos +1; cpos
        }
      val clause_position = clause_indices(findex)
      expformulas(findex) match {
        case fol.Neg(_) => (c.negative(clause_position-1), false, termpos)
        case _ => (c.positive(clause_position-1), true, termpos)
      }
  }

  def heading_twos(l:List[Int], twos : Int) : (Int, List[Int]) = l match {
    case 2::xs => heading_twos(xs, 1+twos)
    case _ => (twos, l)
  }

  def index_at(formulas : List[HOLFormula], pos : List[Int]) : (Int, List[Int]) = {
    val (twos, rest) = heading_twos(pos,0)
    /* there is an ambuguity: the first 1 after the twos might be an index into the literal or select head of the list there*/
    if (twos < formulas.length -1) {
      //we did not choose the last element
      val dropped = pos drop (twos)
      dropped match {
        case 1::1::ys =>
          formulas(twos) match {
            case fol.Neg(_) => (twos, ys)
            case _ => (twos, 1::ys)
        }

        case 1::xs =>
          (twos, xs)
        case _ => throw new Exception("Error parsing position - expected the remaininng position "+pos+" to start with 1.")
      }

    } else if (twos == formulas.length -1) {
      //we choose the last element, but have to check the next one
      val lastpos = formulas.length-1
      val dropped = pos drop (lastpos)
      dropped match {
        case Nil => (lastpos, rest)
        case 1::xs => formulas(lastpos) match {
          case fol.Neg(_) => (lastpos, xs)
          case _ => (lastpos, 1::xs)
        }
        case _ => (lastpos, dropped)
      }
    } else /* twos >= length */{
      //means we chose the last element, since the next one is a two, the position cannot denote the inside of a negation
      ( formulas.size-1, pos drop (formulas.length -1) )
    }

  }

  /*
  def index_at(formulas : List[HOLFormula], pos : List[Int], offset : Int) : (Int, List[Int]) = (formulas, pos) match {
    case (_, Nil) => (offset, Nil)
    case (x::y::Nil, p::ps) => p match {
      //this case, 1 means
      case 1 => x match {
        case fol.Neg(_) =>
      }

    }
  }
    */

/*
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
*/
  /*
  def get_literal_by_position_(pos:List[SExpression], clauseexp : List[HOLFormula], index : Int) : (Int, immutable.List[SExpression]) = {
    clauseexp match {
      case Nil =>
        throw new Exception("Error parsing position in SExpression!")
      case x::xs =>
        pos match {
          case Nil => (index, pos) //TODO:check if this is really correct
          case lisp.Atom("1") :: rest =>
           // get_literal_by_position_(rest, List(x), index+1)
            (index, rest)
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
  } */


  //term replacement
  //TODO: refactor replacement for lambda expressions
  def replaceTerm_by_in_at(what : FOLTerm, by : FOLTerm, exp : fol.FOLExpression, pos : immutable.List[Int] )
    : fol.FOLExpression = pos match {
      case p::ps =>
        exp match {
          case fol.Atom(sym, args) =>
            require(1<=p && p <= args.length, "Error in parsing replacement: invalid argument position in atom!")
            val (args1, rterm::args2) = args.splitAt(p-1)
            fol.Atom(sym, (args1 ++ List(replaceTerm_by_in_at(what,by,rterm, ps ).asInstanceOf[FOLTerm]) ++ args2))
          case fol.Function(sym, args) =>
            require(1<=p && p <= args.length, "Error in parsing replacement: invalid argument position in function!")
            val (args1, rterm::args2) = args.splitAt(p-1)
            fol.Function(sym, (args1 ++ List(replaceTerm_by_in_at(what,by,rterm, ps ).asInstanceOf[FOLTerm]) ++ args2))
          case _ => throw new Exception("Error in parsing replacement: unexpected (sub)term "+exp+ " )")
        }

      case Nil =>
        if (exp == what) by else throw new Exception("Error in parsing replacement: (sub)term "+exp+ " is not the expected term "+what)
      //throw new Exception("Error in parsing replacement: cannot replace at formula level!")
    }


  def parse_position(l : immutable.List[SExpression]) : immutable.List[Int] = l match {
    case lisp.Atom(x)::xs => try {
      x.toInt :: parse_position(xs)
    } catch {
      case e:Exception => throw new Exception("Error parsing position: cannot convert atom "+x+" to integer!")
    }
    case Nil => Nil
    case x::_ => throw new Exception("Error parsing position: unexpected expression "+x)
    case _ => throw new Exception("Error parsing position: unexpected expression "+l)
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
  def is_prologstyle_variable(s: String) = prolog_variable_regexp.findFirstIn(s) match {
      case None => false
      case _ => true
    }

  val ivy_variable_regexp = """^v[0-9]+$""".r
  def is_ivy_variable(s: String) = ivy_variable_regexp.findFirstIn(s) match {
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
    if (name == "=") {
      require(args.length == 2, "Error parsing equality: = must be a binary predicate!")
      fol.Equation(argterms(0), argterms(1))
    } else {
      fol.Atom(sym, argterms)
    }

  }


  //some names are escaped for ivy, see also  LADR-2009-11A/ladr/ivy.c in the Prover9 source
  val ivy_escape_table = Map[String,String]( ("zero_for_ivy","0"),
                                             ("one_for_ivy","1"),
                                             ("quote_for_ivy","'"),
                                             ("backslash_for_ivy","\\\\"),
                                             ("at_for_ivy","@"),
                                             ("meet_for_ivy","^"))
  def rewrite_name(s:String) : String = if (ivy_escape_table contains s) ivy_escape_table(s) else s

  val symbol_nil = new ConstantStringSymbol("nil")
  def parse_term(ts : SExpression, is_variable_symbol : String => Boolean) : FOLTerm = ts match {
    case lisp.Atom(name) =>
      val rname = rewrite_name(name)
      if (is_variable_symbol(rname))
        fol.FOLVar(new VariableStringSymbol(rname))
      else
        fol.FOLConst(new ConstantStringSymbol(rname))
    //the proof might contain the constant nil which is parsed to an empty lisp.List. in this case the empty list
    //corresponds to a constant
    case lisp.List(lisp.List(Nil)::Nil) =>
      fol.FOLConst(symbol_nil)
    case lisp.List(lisp.Atom(name)::args) =>
      val rname = rewrite_name(name)
      if (is_variable_symbol(rname)) throw new Exception("Parsing Error: Function name "+rname+" does not conform to naming conventions.")
      fol.Function(new ConstantStringSymbol(rname), args.map(parse_term(_, is_variable_symbol)) )
    case _ =>
      throw new Exception("Parsing Error: Unexpected expression "+ts+" in parsing of a term.")
  }


}
