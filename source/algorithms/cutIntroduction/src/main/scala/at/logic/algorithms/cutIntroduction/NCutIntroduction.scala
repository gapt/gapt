/**
 * Cut introduction algorithm
 *
 *
 */
package at.logic.algorithms.cutIntroduction

import Deltas._
import at.logic.algorithms.interpolation._
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.resolution._
import at.logic.calculi.expansionTrees.{ExpansionTree, ExpansionSequent, toSequent, quantRulesNumber => quantRulesNumberET}
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.calculi.resolution.FClause
import at.logic.language.fol._
import at.logic.language.hol.HOLFormula
import at.logic.provers.Prover
import at.logic.provers.minisat.MiniSATProver
import at.logic.provers.prover9.Prover9Prover
import at.logic.transformations.herbrandExtraction.extractExpansionTrees
import at.logic.transformations.herbrandExtraction.extractExpansionTrees
import at.logic.utils.constraint.{Constraint, NoConstraint, ExactBound, UpperBound}
import at.logic.utils.executionModels.timeout._
import at.logic.utils.logging.Logger

class NCutIntroException(msg: String) extends Exception(msg)
class NCutIntroUncompressibleException(msg: String) extends NCutIntroException(msg)

/**
 * Thrown if Extended Herbrand Sequent is unprovable. In theory this does not happen.
 * In practice it does happen if the method used for searching a proof covers a too
 * weak theory (e.g. no equality) or is not complete.
 **/
class NCutIntroEHSUnprovableException(msg: String) extends NCutIntroException(msg)


/** Cut introduction with cut formulas of the form [forall x1,...,xn] F.
  * In contrast to regular cut introduction, the cut formulas may contain more than one
  * universally quantified variable.
  */
object NCutIntroduction extends Logger {

  /** Performs cut introduction on an LK proof and returns 
    * an LK proof with cut if a cut formula can be found.
    *
    * @param proof The cut-free LK proof into which to introduce a cut.
    * @param numVars a constraint (see utils.contstraint) on the number of variables to
    *          introduce. Valid constraints are NoConstraint, ExactBound(1), UpperBound(n) (n>0).
    * @param prover The prover to use for tautology checks.
    * @return The LK proof with cut if cut introduction was successful and None otherwise.
    *         The cause of failure will be printed on the console.
    */
  def apply(proof: LKProof, numVars: Constraint[Int], prover: Prover = new DefaultProver(), n: Int) : Option[LKProof] = apply( extractExpansionTrees( proof ), numVars, prover, n)

  /** Performs cut introduction on an LK proof and returns 
    * an LK proof with cut if a cut formula can be found.
    *
    * @param ep: The sequent of expansion trees to which cut-introduction is to be applied.
    * @param numVars a constraint (see utils.contstraint) on the number of variables to
    *          introduce. Valid constraints are NoConstraint, ExactBound(1), UpperBound(n) (n>0).
    * @param prover: The prover used for checking validity and constructing the final proof.
                     Default: use MiniSAT for validity check, LK proof search for proof building.
    * @return The LK proof with cut if cut introduction was successful and None otherwise.
    *         The cause of failure will be printed on the console.
    */
  def apply(ep: ExpansionSequent, numVars: Constraint[Int], prover: Prover, n: Int) : Option[LKProof] = {
    val deltaVec = numVars match {
      case NoConstraint => { println("Using UnboundedVariableDelta."); Some(new UnboundedVariableDelta()) }
      case ExactBound(1) => { println("Using OneVariableDelta."); Some(new OneVariableDelta()) }
      case UpperBound(n) => { println("Using ManyVariableDelta."); Some(new ManyVariableDelta(n)) }
      case ExactBound(n) => {
        println("cut Introduction with exactly n (n>1) variables is currently not supported!")
        error("Used constraint 'ExactBound(" + n + ")' in NCutIntroduction.")
        None
      }
      case c@_ => {
        println("Invalid constraint! Only NoConstraint, ExactBound and UpperBound are permissible!")
        error("Used invalid constraint in NCutIntroduction: " + c)
        None
      }
    }

    if (deltaVec.isEmpty) None else {
      try {
        Some(apply(ep, prover, deltaVec.get, n))
      } catch {
        case ex : NCutIntroException => {
          println(ex.toString());
          None
        }
      }
    }
  }

  /** Performs cut introduction with a given delta vector.
    *
    * The choice of delta vector determines how many variables the cut formula may contain.
    * E.g.: OneVariableDelta leads to cut formulas [forall x] F, UnboundedVariableDelta leads to [forall x1,...xn] F (for a priori unknown n).
    */
  private def apply(ep: ExpansionSequent, prover: Prover, delta: DeltaVector, n: Int) : LKProof = {

    val endSequent = toSequent(ep)
    println("\nEnd sequent: " + endSequent)

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val termsTuples = TermsExtraction(ep)
    val terms = new FlatTermSet(termsTuples)
    println("Size of term set: " + terms.termset.size)

    var beginTime = System.currentTimeMillis

    //val grammars = ComputeGrammars(terms, delta)

    val grammars = TreeGrammarDecomposition(terms.termset,n)
    //println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      println("ERROR CUT-INTRODUCTION: No grammars found. Cannot compress!")
      throw new CutIntroUncompressibleException("\nNo grammars found." +
        " The proof cannot be compressed using a cut with one universal quantifier block.\n")
    }

    // Compute the proofs for each of the smallest grammars
    //val smallest = grammars.head.size
    //val smallestGrammars = grammars.filter(g => g.size == smallest)

    //println( "Smallest grammar-size: " + smallest )
    //println( "Number of smallest grammars: " + smallestGrammars.length )

    debug("Improving solution...")

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:Grammar, prover:Prover) : Option[(LKProof, ExtendedHerbrandSequent)] = {
      //debug( "building proof for grammar " + grammar.toPrettyString )

      val cutFormula0 = computeCanonicalSolution(endSequent, grammar)

      debug("[buildProof] cutFormula0: " + cutFormula0)
      debug("[buildProof] grammar: " + grammar)

      val ehs = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      val ehs1 = MinimizeSolution(ehs, prover)
      debug ( "building final proof" )
      val proof = buildProofWithCut(ehs1, prover)
      debug ( "done building final proof" )

      if (proof.isDefined) { Some((CleanStructuralRules(proof.get),ehs1)) } else { None }
    }

    debug("   NCUTINTRO:")
    debug("   grammar: " + grammars(0))

    val proofs = grammars.map(buildProof(_, prover)).filter(proof => proof.isDefined).map(proof => proof.get)

    //debug("Improve solutions time: " + (System.currentTimeMillis - beginTime))

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    debug("\nGrammar chosen: {" + ehs.grammar.u + "} o {" + ehs.grammar.s + "}")
    debug("\nMinimized cut formula: " + sanitizeVars(ehs.cutFormula) + "\n")

    smallestProof
  }

  /** Computes the canonical solution with multiple quantifiers from a generalized grammar.
    */
  def computeCanonicalSolution(seq: Sequent, g: Grammar) : FOLFormula = {

    val flatterms = g.flatterms
    val varName = "x"

    debug("===============================================================")
    debug("   g.u:\n")
    debug(g.u.toString())
    debug("===============================================================")
    debug("g.eigenvariables: \n")
    debug(g.eigenvariables.toString())
    debug("===============================================================")
    debug("    g.s:\n")
    debug(g.s.toString())
    debug("===============================================================")

    val xFormulas = g.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val freeVars = freeVariables(term)

      // Taking only the terms that contain alpha
      if( !freeVars.intersect(g.eigenvariables).isEmpty ) {
        debug("      found terms with alphas!")
        debug("      term: " + term)
        //TODO: here a NullPointerException is raised. Probably because of flatterms=null. But WHY?
        val terms = flatterms.getTermTuple(term)
        val f = flatterms.getFormula(term)

        //Some subset of g's eigenvariables occurs in every term. This generates
        //substitutions to replace each occurring EV a_i with a quantified variables x_i.
        val xterms = terms.map(t => {
          val vars = createFOLVars(varName, g.eigenvariables.length+1)
          val allEV = g.eigenvariables.zip(vars)
          val occurringEV = collectVariables(t).filter(isEigenvariable(_:FOLVar, g.eigenvariable)).distinct

          debug("allEV: " + allEV)
          debug("occurringEV: " + occurringEV)
          debug("filteredEV: " + allEV.filter(e => occurringEV.contains(e._1)))

          val res = allEV.filter(e => occurringEV.contains(e._1)).foldLeft(t)((t,e) => Substitution(e._1, e._2).apply(t))

          debug("result: " + res)

          //edge case: The current term is constant. In this case, we don't instantiate the variables inside, but leave it as is.
          if (collectVariables(t).filter(isEigenvariable(_:FOLVar, g.eigenvariable)).isEmpty) { t } else { res }
        })

        debug("ComputeCanoicalSolutionG:")
        debug("   f: " + f)
        debug("   terms: " + terms)
        debug("   xterms: " + xterms)
        debug("   eigenvariables: " + g.eigenvariables)
        debug("---------------------------------------------")

        instantiateAll(f, xterms) :: acc
      }
      else acc
    }

    (0 to (g.eigenvariables.size-1)).reverse.toList.foldLeft(And(xFormulas)){(f, n) => AllVar(FOLVar(varName + "_" + n), f)}
  }



  /** Builds the final proof out of an extended Herbrand sequent.
    *
    * For details, see p.5 of "Algorithmic Introduction of Quantified Cuts (Hetzl et al 2013)".
    */
  def buildProofWithCut(ehs: ExtendedHerbrandSequent, prover: Prover) : Option[LKProof] = {

    val endSequent = ehs.endSequent
    val cutFormula = sanitizeVars(ehs.cutFormula)
    val grammar = ehs.grammar
    val flatterms = grammar.flatterms

    //Instantiate the cut formula with α_0,...,α_n-1, where n is the number of alphas in the ehs's grammar.
    //partialCutLeft.last ist the all-quantified cut formula, partialCutLeft.head ist the cut formula, with its
    //whole initial quantifier block instantiated to α_0,...,α_n-1.
    val alphas = createFOLVars("α", ehs.grammar.numVars)

    debug("grammar (u,S): ")
    debug(ehs.grammar.u.toString)
    debug(ehs.grammar.s.toString)
    debug("alphas: " + alphas)
    //val partialCutLeft = (0 to alphas.length).toList.reverse.map(n => instantiateFirstN(cutFormula,alphas,n)).toList
    val cutLeft = instantiateAll(cutFormula, alphas)

    debug("cutLeft = " + cutLeft)

    //Fully instantiate the cut formula with s[j=1...n][i] for all i.
    val cutRight = grammar.s.toList.foldRight(List[FOLFormula]()) { case (t, acc) =>
      (t.foldLeft(cutFormula){case (f, sval) => instantiate(f, sval)}) :: acc
    }

    //leftBranch and rightBranch correspond to the left and right branches of the proof in the middle of
    //p. 5; untilCut merges these together with a cut.

    //debug( "calling solvePropositional" )
    //solvePropositional need only be called with the non-instantiated cutLeft (with the quantifier block in front)
    debug("===FSEQUENT===")
    debug("ehs.antecedent: " + ehs.antecedent)
    debug("ehs.antecedent_alpha: " + ehs.antecedent_alpha)
    debug("cutFormula: " + cutFormula)
    debug("   instatiated with alphas: " + alphas)
    debug("   resulting in cutLeft: " + cutLeft)
    debug("ehs.succedent: " + ehs.succedent)
    debug("ehs.succedent_alpha: " + ehs.succedent_alpha)
    debug(FSequent((ehs.antecedent ++ ehs.antecedent_alpha), (cutLeft +: (ehs.succedent ++ ehs.succedent_alpha))).toString())

    val seq = FSequent((ehs.antecedent ++ ehs.antecedent_alpha), (cutLeft +: (ehs.succedent ++ ehs.succedent_alpha)))


    val proofLeft = prover.getLKProof(seq)
    val leftBranch = proofLeft match {
      case Some(proofLeft1) =>
        val s1 = uPart(grammar.u.filter(t => !freeVariables(t).intersect(grammar.eigenvariables).isEmpty), proofLeft1, flatterms)

        debug("=======================")
        debug("s1:")
        debug(s1.toString())
        debug("=======================")
        debug("CF: " + cutFormula)
        debug("alphas: " + alphas)

        //Add sequents to all-quantify the cut formula in the right part of s1
        ForallRightBlock(s1, cutFormula, alphas)

      case None => throw new CutIntroEHSUnprovableException("ERROR: propositional part is not provable.")
    }

    val seq2 = FSequent(cutRight ++ ehs.antecedent, ehs.succedent)
    val proofRight = prover.getLKProof(seq2)
    val rightBranch = proofRight match {
      case Some(proofRight1) => sPart(cutFormula, grammar.s, proofRight1)
      case None => throw new CutIntroEHSUnprovableException("ERROR: propositional part is not provable: " + FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
    }
    //debug( "done calling solvePropositional" )

    //Merge the left and right branches with a cut.
    val untilCut = CutRule(leftBranch, rightBranch, cutFormula)

    // Contracting the formulas that go to both branches of the cut
    val contractAnt = ehs.antecedent.foldRight(untilCut.asInstanceOf[LKProof]) { case (f, premise) => ContractionLeftRule(premise, f) }
    val contractSucc = ehs.succedent.foldRight(contractAnt.asInstanceOf[LKProof]) { case (f, premise) => ContractionRightRule(premise, f) }

    // Instantiating constant terms from U
    Some(uPart(grammar.u.filter(t => freeVariables(t).intersect(grammar.eigenvariables).isEmpty), contractSucc, flatterms))
  }

  // Both methods bellow are responsible for generating the instances of 
  // end-sequent ancestors with the terms from the set U
  def genWeakQuantRules(f: FOLFormula, lst: List[FOLTerm], ax: LKProof) : LKProof = (f, lst) match {
    case (_, Nil) => ax
    case (AllVar(_,_), h::t) =>
      val newForm = instantiate(f, h)
      ForallLeftRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
    case (ExVar(_,_), h::t) =>
      val newForm = instantiate(f, h)
      ExistsRightRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
  }

  /** Proves the u-part of a grammar.
    *
    */
  def uPart(us: List[types.U], ax: LKProof, flatterms: FlatTermSet) : LKProof = {
    us.foldLeft(ax) {
      case (ax, term) =>
        //Get the arguments of a single u
        val terms = flatterms.getTermTuple(term)
        val f = flatterms.getFormula(term)

        f match {
          case AllVar(_, _) =>
            try {
              ContractionLeftRule(genWeakQuantRules(f, terms, ax), f)
            }
            catch {
              // Not able to contract the formula because it was the last
              // substitution
              case e: LKRuleCreationException => genWeakQuantRules(f, terms, ax)
            }
          case ExVar(_, _) =>
            try {
              ContractionRightRule(genWeakQuantRules(f, terms, ax), f)
            }
            catch {
              case e: LKRuleCreationException => genWeakQuantRules(f, terms, ax)
            }
        }
    }
  }

  /** Given a proof in which the cut formula occurs in
    * fully instantiated form (with the terms s from a grammar),
    * this method extends it by universally quantifying those terms
    * to get the cut formula cf back.
    *
    * Example: if f(a,b) occurs in p, the cut formula is [forall x,y] f(x,y)
    * and the terms are [[ a],[b]],
    * then sPart extends the proof with two ForallLeft-rules, universally
    * quantifying first a, then b, creating the cut formula in the bottom.
    * If there are multiple terms in p, the cut formula is introduced multiple
    * times and merged into only one occurrence via contraction.
    *
    * @param cf The cut formula with a quantifier block.
    * @param s The s-Part of a grammar, where each element corresponds
    *        to the values of one variable.
    * @param p The proof to be extended with ForallLeft-rules below.
    * @return p, extended with ForallLeft- and ContractionLeft-rules,
    *         containing extactly one occurrence of the cut formula.
    */
  def sPart(cf: FOLFormula, s: types.S, p: LKProof) : LKProof = {
    var first = true;

    s.toList.foldLeft(p) { case (p,t) =>

      //1. Partially instantiate the cut formula.
      //val pcf = (0 to t.length).toList.reverse.map(n => instantiateFirstN(cf,t,n)).toList

      //2. Starting from p, in which pcf[0] occurs, work down, adding quantifiers, until we get 
      //   the fully quantified cf back.
      val newP = ForallLeftBlock(p, cf, t)

      //3. If this is not the first time we build cf, 
      //   cf is already present in p and we can do away with its second,
      //   newly generated instance through a contraction rule.
      if (first) {
        first = false
        newP
      }
      else {
        ContractionLeftRule(newP, cf)
      }
    }
  }

  /**
   * A quick sanitizing function which renames the variables of the cut formula
   * from x_0,x_1,... to x,y,...
   * Variables beyond x_5 are left unchanged.
   */
  def sanitizeVars(f: FOLFormula) = {
    val sanitizedVars = List[(String,String)](("x","x_0"),("y","x_1"),("z","x_2"),("u","x_3"),("v","x_4"),("w","x_5")).map(
      v => (FOLVar(v._1),FOLVar(v._2)) )

    sanitizedVars.foldLeft(f){(f, v) => f match {
      case AllVar(_, _) => replaceLeftmostBoundOccurenceOf(v._2, v._1,f)._2
      case _ => f
    }}
  }
}

