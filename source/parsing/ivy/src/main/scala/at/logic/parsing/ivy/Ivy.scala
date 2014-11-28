
package at.logic.parsing.ivy

import at.logic.parsing.lisp.{List => LispList, Atom => LispAtom, Cons => LispCons, SExpression, SExpressionParser}
import at.logic.language.hol.HOLFormula
import at.logic.language.fol._
import at.logic.calculi.resolution.Clause
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.occurrences
import at.logic.language.lambda.types.Ti

/**
 * Implements parsing of ivy format: https://www.cs.unm.edu/~mccune/papers/ivy/ into Ivy's Resolution calculus.
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

  var debug : Boolean = false
  private def debug(a:Any) : Unit = if (debug) { println("Debug: "+a.toString) }

  // the type synoyms should make the parsing functions more readable
  type ProofId = String
  type ProofMap = Map[ProofId, IvyResolutionProof]
  type Position = List[Int]


  //decompose the proof object to a list and hand it to parse(exp: List[SExpression], found_steps : ProofMap )
  def parse(exp: SExpression, is_variable_symbol : (String => Boolean) ) : IvyResolutionProof =  exp match {
    case LispList(Nil) => throw new Exception("Trying to parse an empty proof!")
    case LispList(l) => parse(l, Map[String, IvyResolutionProof](), is_variable_symbol ) // extract the list of inferences from exp
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
      case LispList(LispAtom(id) :: _) => () //debug("processing inference "+id)
      case _ => ()
    }
    exp match {
      /* ================== Atom ========================== */
      case LispList( LispAtom(id):: LispList(LispAtom("input")::Nil) :: clause :: _  )  => {
        val fclause = parse_clause(clause, is_variable_symbol)

        val inference = InitialClause(id,clause,
          Clause(fclause.antecedent map (occurrences.factory.createFormulaOccurrence(_, Nil)) ,
                 fclause.succedent map (occurrences.factory.createFormulaOccurrence(_, Nil))))

        require(inference.root.toFSequent setEquals fclause, "Error in Atom parsing: required result="+fclause+" but got: "+inference.root)
        (id, found_steps + ((id, inference)) )
      }

      /* ================== Instance ========================== */
      case LispList( LispAtom(id):: LispList(LispAtom("instantiate")::LispAtom(parent_id):: subst_exp::Nil) :: clause :: rest  )  => {
        val parent_proof = found_steps(parent_id)
        val sub : Substitution = parse_substitution(subst_exp, is_variable_symbol)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)

        def connect(ancestors: Seq[FormulaOccurrence], formulas: Seq[HOLFormula]) :
        Seq[FormulaOccurrence] =
          (ancestors zip formulas) map ( (v: (FormulaOccurrence, HOLFormula)) =>
            occurrences.factory.createFormulaOccurrence(v._2, List(v._1)))

        val inference = Instantiate(id,clause, sub,
          Clause(connect(parent_proof.vertex.antecedent, fclause.antecedent),
                 connect(parent_proof.vertex.succedent, fclause.succedent)), parent_proof)

        require(inference.root.toFSequent setEquals fclause, "Error in Instance parsing: required result="+fclause+" but got: "+inference.root)
        (id, found_steps + ((id, inference)) )


      }

      /* ================== Resolution ========================== */
      case LispList( LispAtom(id):: LispList(LispAtom("resolve")::
                         LispAtom(parent_id1):: LispList(position1) ::
                         LispAtom(parent_id2):: LispList(position2) :: Nil) ::
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
                val focc = c1.antecedent(pos1).factory.createFormulaOccurrence(x, c1.antecedent(pos1).parents  )
                val rec = connect(Clause(c1.antecedent.filterNot(_ == c1.antecedent(pos1)), c1.succedent), c2, FSequent(xs,ys))
                Clause(focc :: rec.antecedent.toList, rec.succedent)
              } else {
                val pos2 = c2.antecedent indexWhere (_.formula == x)
                if (pos2 >= 0) {
                  val focc =  c2.antecedent(pos2).factory.createFormulaOccurrence(x, c2.antecedent(pos2).parents )
                  val rec = connect(c1, Clause(c2.antecedent.filterNot(_ == c2.antecedent(pos2)), c2.succedent), FSequent(xs,ys))
                  Clause(focc :: rec.antecedent.toList, rec.succedent)
                } else throw new Exception("Error in parsing resolution inference: resolved literal "+x+" not found!")
              }
            //then succedent
            case FSequent(Nil, y::ys ) =>
              val pos1 = c1.succedent indexWhere (_.formula == y)
              if (pos1 >= 0) {
                val focc = c1.succedent(pos1).factory.createFormulaOccurrence(y, c1.succedent(pos1).parents )
                val rec = connect(Clause(c1.antecedent, c1.succedent.filterNot(_ == c1.succedent(pos1))), c2, FSequent(Nil,ys))
                Clause(rec.antecedent, focc :: rec.succedent.toList)
              } else {
                val pos2 = c2.succedent indexWhere (_.formula == y)
                if (pos2 >= 0) {
                  val focc = c2.succedent(pos2).factory.createFormulaOccurrence(y, c2.succedent(pos2).parents  )
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
      case LispList( LispAtom(id):: LispList(LispAtom("flip")::LispAtom(parent_id)::LispList(position)::Nil) :: clause :: rest  )  =>
        val parent_proof = found_steps(parent_id)
        val fclause = parse_clause(clause, is_variable_symbol)
        val (occ, polarity, _) = get_literal_by_position(parent_proof.root, position, parent_proof.clause_exp, is_variable_symbol)
        //require(polarity == true, "Flipped literals must be positive!"+parent_proof.clause_exp+" -> "+clause)

        occ.formula match {
          case Equation(left,right) =>
            //the negative literals are the same
            def connect_directly(x:FormulaOccurrence) = x.factory.createFormulaOccurrence(x.formula, x::Nil)

            polarity match {
              case true =>
                val neglits = parent_proof.root.negative map connect_directly
                val (pos1, pos2) = parent_proof.root.positive.splitAt( parent_proof.root.positive.indexOf(occ))
                val (pos1_, pos2_) = (pos1 map connect_directly, pos2 map  connect_directly)
                val flipped = occ.factory.createFormulaOccurrence(Equation(right, left), occ::Nil)
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
                val flipped = occ.factory.createFormulaOccurrence(Equation(right, left), occ::Nil)
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
      case LispList( LispAtom(id)::
                      LispList(LispAtom("paramod")::LispAtom(modulant_id)::LispList(mposition)::
                                                      LispAtom(parent_id)::  LispList(pposition):: Nil) ::
                      clause :: rest  )  =>
        val modulant_proof = found_steps(modulant_id)
        val parent_proof = found_steps(parent_id)
        val fclause = parse_clause(clause, is_variable_symbol)
        val (mocc, mpolarity, direction) = get_literal_by_position(modulant_proof.root, mposition, modulant_proof.clause_exp, is_variable_symbol)
        require(direction == List(1) || direction == List(2), "Must indicate if paramod or demod!")
        val orientation = if (direction.head == 1) true else false //true = paramod (left to right), false = demod (right to left)

        debug("found occurrence of equation: "+mocc+" at pos "+mposition)
        require(mpolarity == true, "Paramodulated literal must be positive!")
        val (pocc, polarity, int_position) = get_literal_by_position(parent_proof.root, pposition, parent_proof.clause_exp, is_variable_symbol)
        debug("found occurrence of target formula:"+pocc+" at pos "+pposition)

        mocc.formula match {
          case Equation(left,right) =>
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
                val paraformula = if (orientation)
                                    replaceTerm_by_in_at(left, right, pocc.formula.asInstanceOf[FOLFormula], int_position ).asInstanceOf[FOLFormula]
                                  else
                                    replaceTerm_by_in_at(right, left, pocc.formula.asInstanceOf[FOLFormula], int_position ).asInstanceOf[FOLFormula]
                val para = pocc.factory.createFormulaOccurrence(paraformula,  mocc::pocc::Nil)
                /*debug("Context is:" +ppos)
                debug("Context is:" +pos1_)
                debug("Context is:" +pos2_)
                debug("Together:"+ (ppos ++ pos1_  ++ pos2_.tail)) */

                val inferred_clause = Clause(pneg ++ neglits, ppos ++ pos1_ ++ List(para) ++ pos2_.tail)
                debug("inferred clause: " + inferred_clause)

                val inference = Paramodulation(id, clause, int_position, para, orientation, inferred_clause, modulant_proof, parent_proof)
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
                val paraformula = if (orientation)
                  replaceTerm_by_in_at(left, right, pocc.formula.asInstanceOf[FOLFormula], int_position ).asInstanceOf[FOLFormula]
                else
                  replaceTerm_by_in_at(right, left, pocc.formula.asInstanceOf[FOLFormula], int_position ).asInstanceOf[FOLFormula]

                val para = pocc.factory.createFormulaOccurrence(paraformula,  mocc::pocc::Nil)
                val inferred_clause = Clause(pneg ++ neg1_ ++ List(para) ++ neg2_.tail, ppos ++ poslits)

                val inference = Paramodulation(id, clause, int_position, para, orientation, inferred_clause, modulant_proof, parent_proof)

                require(inference.root.toFSequent setEquals fclause, "Error in Paramodulation parsing: required result="+fclause+" but got: "+inference.root)
                //debug("new Paramod rule: "+id+ " : "+inference)
                (id, found_steps + ((id, inference)))
            }


          case _ =>
            throw new Exception("Error parsing position in paramod rule: literal "+mocc.formula+" is not the equality predicate.")

        }

      /* ================== Propositional ========================== */
      case LispList( LispAtom(id):: LispList(LispAtom("propositional")::LispAtom(parent_id)::Nil) :: clause :: rest  )  => {
        val parent_proof = found_steps(parent_id)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)

        def list_withoutn[A](l : List[A], n:Int) : List[A] = l match {
          case x::xs =>
            if (n==0) xs else x::list_withoutn(xs,n-1)
          case Nil => Nil
        }

        //connects ancestors to formulas
        def connect(ancestors: List[FormulaOccurrence], formulas: List[HOLFormula]) :
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
        def connect_(ancestors: List[FormulaOccurrence], formulas: List[HOLFormula]) :
            (List[FormulaOccurrence], List[FormulaOccurrence]) = {
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
        def connect_missing(targets : List[FormulaOccurrence], missing : List[FormulaOccurrence])
           : List[FormulaOccurrence] = missing match {
          case x::xs =>
            debug("trying to append "+x+" to possibilities "+targets)
            val targets_ = connect_missing_(targets, x)
            connect_missing(targets_, xs)
          case Nil =>
            targets
        }

        //connects one missing occurence to possible tagets, returns list of updated targets
        def connect_missing_(targets : List[FormulaOccurrence], missing : FormulaOccurrence)
           : List[FormulaOccurrence] = targets match {
          case x::xs =>
            if (missing.formula == x.formula)
              List(x.factory.createFormulaOccurrence(x.formula, List(missing) ++ x.parents)) ++ xs
            else
              List(x) ++ connect_missing_(xs, missing)
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
      case LispList( LispAtom(id)::
        LispList(LispAtom("new_symbol")::LispAtom(parent_id):: Nil) ::
        clause :: rest  ) =>

        val parent_proof = found_steps(parent_id)
        val fclause : FSequent = parse_clause(clause, is_variable_symbol)
        //println("New Symbol Rule: "+fclause)
        //println("Parent Rule:     "+parent_proof.root)
        require(fclause.antecedent.isEmpty, "Expecting only positive equations in parsing of new_symbol rule "+id)
        require(fclause.succedent.size == 1, "Expecting exactly one positive equation in parsing of new_symbol rule "+id)

        val Equation(l,r) = fclause.succedent(0)

        val nclause = Clause(Nil, List(parent_proof.root.occurrences(0).factory.createFormulaOccurrence(fclause.succedent(0), Nil) ) )
        val const : FOLConst = r match {
          case f@FOLConst(_) => f.asInstanceOf[FOLConst]
          case _ => throw new Exception("Expecting right hand side of new_symbol equation to be the introduced symbol!")
        }

        //println("const symbol="+const + " replaced by="+l)
        val inference = NewSymbol(id, clause, nclause.succedent(0), const, l, nclause, parent_proof )

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
    val ipos = parse_position(pos)
    val (iformula, termpos) = parse_clause_frompos(clauseexp, ipos, is_variable_symbol)
    //Remark: we actually return the first occurrence of the formula, not the one at the position indicated as
    //        it should not make a difference. (if f occurs twice in the clause, it might be derived differently
    //        but we usually don't care for that)
    iformula match {
      case a@Atom(sym, args) =>
        c.positive.find(_.formula == a) match {
          case Some(occ) =>
            (occ, true, termpos)
          case None =>
            throw new Exception("Error in getting literal by position! Could not find "+iformula+" in "+c)
        }

      case Neg(a@Atom(sym,args)) =>
        c.negative.find(_.formula == a) match {
          case Some(occ) =>
            (occ, false, termpos)
          case None =>
            throw new Exception("Error in getting literal by position! Could not find "+iformula+" in "+c)
        }
    }
  }


  //term replacement
  //TODO: refactor replacement for lambda expressions
  def replaceTerm_by_in_at(what : FOLTerm, by : FOLTerm, exp : FOLExpression, pos : List[Int] )
    : FOLExpression = pos match {
      case p::ps =>
        exp match {
          case Atom(sym, args) =>
            require(1<=p && p <= args.length, "Error in parsing replacement: invalid argument position in atom!")
            val (args1, rterm::args2) = args.splitAt(p-1)
            Atom(sym, (args1 ++ List(replaceTerm_by_in_at(what,by,rterm, ps ).asInstanceOf[FOLTerm]) ++ args2))
          case Function(sym, args) =>
            require(1<=p && p <= args.length, "Error in parsing replacement: invalid argument position in function!")
            val (args1, rterm::args2) = args.splitAt(p-1)
            Function(sym, (args1 ++ List(replaceTerm_by_in_at(what,by,rterm, ps ).asInstanceOf[FOLTerm]) ++ args2))
          case _ => throw new Exception("Error in parsing replacement: unexpected (sub)term "+exp+ " )")
        }

      case Nil =>
        if (exp == what) by else throw new Exception("Error in parsing replacement: (sub)term "+exp+ " is not the expected term "+what)
      //throw new Exception("Error in parsing replacement: cannot replace at formula level!")
    }


  def parse_position(l : List[SExpression]) : List[Int] = l match {
    case LispAtom(x)::xs => try {
      x.toInt :: parse_position(xs)
    } catch {
      case e:Exception => throw new Exception("Error parsing position: cannot convert atom "+x+" to integer!")
    }
    case Nil => Nil
    case x::_ => throw new Exception("Error parsing position: unexpected expression "+x)
    case _ => throw new Exception("Error parsing position: unexpected expression "+l)
  }

  def parse_substitution(exp : SExpression, is_variable_symbol : String => Boolean) : Substitution = exp match {
    case LispList(list) =>
      Substitution(parse_substitution_(list, is_variable_symbol))
    case _ => throw new Exception("Error parsing substitution expression "+exp+" (not a list)")
  }

  //Note:substitution are sometimes given as lists of cons and sometimes as two-element list...
  def parse_substitution_(exp : List[SExpression], is_variable_symbol : String => Boolean) : List[(FOLVar, FOLTerm)] = exp match {
    case LispList(vexp::texp)::xs =>
      val v = parse_term(vexp, is_variable_symbol)
      val t = parse_term(LispList(texp), is_variable_symbol)

      v match {
        case v_ : FOLVar =>
          (v_,t) :: parse_substitution_(xs, is_variable_symbol)
        case _ =>
          throw new Exception("Error parsing substitution expression "+exp+": substiution variable was not parsed as variable!")
      }

    case LispCons(vexp, texp)::xs =>
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
        case Neg(formula) =>
          formula match {
            case Atom(_,_) => neg = formula::neg
            case _ => throw new Exception("Error parsing clause: negative Literal "+formula+" is not an atom!")
          }
        case Atom(_,_) =>
              pos = c :: pos
        case _ =>
          throw new Exception("Error parsing clause: formula "+c+" is not a literal!")
      }
    }

    //the literals were prepended to the list, so we have to reverse them to get the original order
    FSequent(neg.reverse, pos.reverse)
  }



  //TODO: merge code with parse_clause_
  def parse_clause_frompos(exp:SExpression, pos : List[Int], is_variable_symbol : String => Boolean) : (HOLFormula, List[Int]) = exp match {
    case LispList( LispAtom("or") :: left :: right :: Nil ) =>
      pos match {
        case 1::rest =>
          left match {
            case LispList( LispAtom("not") :: LispList( LispAtom(name) :: args) :: Nil ) =>
              val npos = if (rest.isEmpty) rest else rest.tail //if we point to a term we have to strip the indicator for neg
              (Neg(parse_atom(name, args, is_variable_symbol)), npos )
            case LispList( LispAtom(name) :: args) =>
              (parse_atom(name, args, is_variable_symbol), rest)
            case _ => throw new Exception("Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object.")
          }
        case 2::rest =>
          parse_clause_frompos(right, rest, is_variable_symbol)
        case _ => throw new Exception("pos "+pos+" did not point to a literal!")
      }

    case LispList( LispAtom("not") :: LispList( LispAtom(name) :: args) :: Nil ) =>
      val npos = if (pos.isEmpty) pos else pos.tail //if we point to a term we have to strip the indicator for neg
      (Neg(parse_atom(name, args, is_variable_symbol)), npos)

    case LispList( LispAtom(name) :: args) =>
      (parse_atom(name, args, is_variable_symbol), pos)

    //the empty clause is denoted by false
    case LispAtom("false") =>
      throw new Exception("Parsing Error: want to extract literal from empty clause!")

    case _ => throw new Exception("Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object.")
  }


  //directly converts a clause as nested or expression into a list with the literals in the same order
  def parse_clause_(exp:SExpression, is_variable_symbol : String => Boolean) : List[HOLFormula] = exp match {
    case LispList( LispAtom("or") :: left :: right :: Nil ) =>
      val rightclause = parse_clause_(right, is_variable_symbol)

      left match {
        case LispList( LispAtom("not") :: LispList( LispAtom(name) :: args) :: Nil ) =>
          Neg(parse_atom(name, args, is_variable_symbol)) :: rightclause
        case LispList( LispAtom(name) :: args) =>
          parse_atom(name, args, is_variable_symbol) :: rightclause
        case _ => throw new Exception("Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object.")
      }


    case LispList( LispAtom("not") :: LispList( LispAtom(name) :: args) :: Nil ) =>
      //Neg(parse_clause(formula, is_variable_symbol) )
      Neg(parse_atom(name, args, is_variable_symbol)) ::Nil

    case LispList( LispAtom(name) :: args) =>
      parse_atom(name, args, is_variable_symbol) :: Nil

    //the empty clause is denoted by false
    case LispAtom("false") =>
      List()

    case _ => throw new Exception("Parsing Error: unexpected element " + exp + " in parsing of Ivy proof object.")
  }

  def parse_atom(name: String, args : List[SExpression],is_variable_symbol : String => Boolean) = {
    if (is_variable_symbol(name)) throw new Exception("Parsing Error: Predicate name "+name+" does not conform to naming conventions.")
    val argterms = args map (parse_term(_, is_variable_symbol))
    if (name == "=") {
      require(args.length == 2, "Error parsing equality: = must be a binary predicate!")
      Equation(argterms(0), argterms(1))
    } else {
      Atom(name, argterms)
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

  def parse_term(ts : SExpression, is_variable_symbol : String => Boolean) : FOLTerm = ts match {
    case LispAtom(name) =>
      val rname = rewrite_name(name)
      if (is_variable_symbol(rname))
        FOLVar(rname)
      else
        FOLConst(rname)
    //the proof might contain the constant nil which is parsed to an empty LispList. in this case the empty list
    //corresponds to a constant
    case LispList(LispList(Nil)::Nil) =>
      FOLConst("nil")
    case LispList(LispAtom(name)::args) =>
      val rname = rewrite_name(name)
      if (is_variable_symbol(rname)) throw new Exception("Parsing Error: Function name "+rname+" does not conform to naming conventions.")
      Function(rname, args.map(parse_term(_, is_variable_symbol)) )
    case _ =>
      throw new Exception("Parsing Error: Unexpected expression "+ts+" in parsing of a term.")
  }


}
