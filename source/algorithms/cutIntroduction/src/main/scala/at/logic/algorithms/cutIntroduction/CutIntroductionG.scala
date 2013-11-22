/**
 * Cut introduction algorithm
 * 
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.calculi.occurrences._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.macroRules._
import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.shlk._
import at.logic.algorithms.interpolation._
import at.logic.algorithms.resolution._
import at.logic.calculi.resolution.base.FClause
import at.logic.utils.logging.Logger
import at.logic.calculi.expansionTrees._
import at.logic.calculi.expansionTrees.multi._
import at.logic.utils.constraint.{Constraint, NoConstraint, ExactBound, UpperBound}
import Deltas._

object CutIntroductionG extends Logger {


  def apply(ep: (Seq[ExpansionTree], Seq[ExpansionTree]), numVars: Constraint[Int]) : Option[LKProof] = {
    val endSequent = toSequent(ep)
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(ep)
    apply(endSequent, termsTuples, numVars)
  }

  def apply(proof: LKProof, numVars: Constraint[Int]) : Option[LKProof] = {
    val endSequent = proof.root
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(proof)
    apply(endSequent, termsTuples, numVars)
  }

  def apply(endSequent: Sequent, termsTuples: Map[FOLFormula, List[List[FOLTerm]]], numVars: Constraint[Int]) : Option[LKProof] = {
    val deltaVec = numVars match {
      case NoConstraint => { println("Using UnboundedVariableDelta."); Some(new UnboundedVariableDelta()) }
      case ExactBound(1) => { println("Using OneVariableDelta."); Some(new OneVariableDelta()) }
      case UpperBound(n) => { println("Using ManyVariableDelta."); Some(new ManyVariableDelta(n)) }
      case ExactBound(n) => {
        println("cut Introduction with exactly n (n>1) variables is currently not supported!")
        error("Used constraint 'ExactBound(" + n + ")' in cutIntroduction.")
        None
      }
      case c@_ => {
        println("Invalid constraint! Only NoConstraint, ExactBound and UpperBound are permissible!")
        error("Used invalid constraint in cutIntroduction: " + c)
        None
      }
    }

    if (deltaVec.isEmpty) None else {
      try {
        Some(apply(endSequent, termsTuples, deltaVec.get))
      } catch {
        case ex : CutIntroException => { println(ex.toString()); None }
      }
    }
  }

  def apply(endSequent: Sequent, termsTuples: Map[FOLFormula, List[List[FOLTerm]]], delta: DeltaVector) : LKProof = {

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val terms = new FlatTermSet(termsTuples)

    /*println("Terms: \n" + terms)
    println("===============================================================")
    println("Termstuples: \n" + termsTuples)
    println("===============================================================")
    println( "\nTerm set: {" + terms.termset + "}" )*/
    //println( "Size of term set: " + terms.termset.size )

    var beginTime = System.currentTimeMillis;

    val grammars = ComputeGeneralizedGrammars(terms, delta)

    //debug("Compute grammars time: " + (System.currentTimeMillis - beginTime))

    println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      println("ERROR CUT-INTRODUCTION: No grammars found. Cannot compress.")
      throw new CutIntroUncompressibleException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier block.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    println( "Smallest grammar-size: " + smallest )
    println( "Number of smallest grammars: " + smallestGrammars.length )

    //println("=============================================================")
    //println("" + smallestGrammars.map(x => (x.toString() + "\n")))

    beginTime = System.currentTimeMillis;
    //debug("Improving solution...")

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:GeneralizedGrammar) = {
      //trace( "building proof for grammar " + grammar.toPrettyString )

      val cutFormula0 = computeCanonicalSolutionG(endSequent, grammar)

      trace("[buildProof] cutFormula0: " + cutFormula0)
      trace("[buildProof] grammar: " + grammar)
    
      val ehs = new GeneralizedExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      val ehs1 = ehs.minimizeSolution
      trace ( "building final proof" )
      val proof = buildFinalProof(ehs)
      trace ( "done building final proof" )
      
      if (proof.isDefined) { Some((proof.get,ehs)) } else { None }
    }

    trace("   CUTINTRO:")
    trace("   smallestGrammars: " + smallestGrammars)

    val proofs = smallestGrammars.map(buildProof).filter(proof => proof.isDefined).map(proof => proof.get)

    //debug("Improve solutions time: " + (System.currentTimeMillis - beginTime))

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    println("\nGrammar chosen: {" + ehs.grammar.u + "} o {" + ehs.grammar.s + "}")  
    println("\nMinimized cut formula: " + sanitizeVars(ehs.cutFormula) + "\n")

    smallestProof
  }

  /** Computes the canonical solution with multiple quantifiers from a generalized grammar.
    *
    */
  def computeCanonicalSolutionG(seq: Sequent, g: GeneralizedGrammar) : FOLFormula = {

    val flatterms = g.flatterms
    val varName = "β"

    trace("===============================================================")
    trace("   g.u:\n")
    trace(g.u.toString())
    trace("===============================================================")
    trace("g.eigenvariables: \n")
    trace(g.eigenvariables.toString())
    trace("===============================================================")
    trace("    g.s:\n")
    trace(g.s.toString())
    trace("===============================================================")

    val xFormulas = g.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val freeVars = term.freeVariables

      // Taking only the terms that contain alpha
      if( !freeVars.intersect(g.eigenvariables.toSet).isEmpty ) {
        trace("      found terms with alphas!")
        trace("      term: " + term)
        val terms = flatterms.getTermTuple(term)
        val f = flatterms.getFormula(term)

        //Some subset of g's eigenvariables occurs in every term. This generates
        //substitutions to replace each occurring EV a_i with a quantified variables x_i.
        val xterms = terms.map(t => {
          val vars = createFOLVars(varName, g.eigenvariables.length+1)
          val allEV = g.eigenvariables.zip(vars)
          val occurringEV = collectVariables(t).filter(isEigenvariable(_:FOLVar, g.eigenvariable)).distinct

          trace("allEV: " + allEV)
          trace("occurringEV: " + occurringEV)
          trace("filteredEV: " + allEV.filter(e => occurringEV.contains(e._1)))

          val res = allEV.filter(e => occurringEV.contains(e._1)).foldLeft(t)((t,e) => FOLSubstitution(t, e._1, e._2))

          trace("result: " + res)

          //edge case: The current term is constant. In this case, we don't instantiate the variables inside, but leave it as is.
          if (collectVariables(t).filter(isEigenvariable(_:FOLVar, g.eigenvariable)).isEmpty) { t } else { res }
        })

        trace("ComputeCanoicalSolutionG:")
        trace("   f: " + f)
        trace("   terms: " + terms)
        trace("   xterms: " + xterms)
        trace("   eigenvariables: " + g.eigenvariables)
        trace("---------------------------------------------")

        val fsubst = f.instantiateAll(xterms)
        f.instantiateAll(xterms) :: acc
      }
      else acc
    }
 
    (0 to (g.eigenvariables.size-1)).reverse.toList.foldLeft(andN(xFormulas)){(f, n) => AllVar(FOLVar(new VariableStringSymbol(varName + "_" + n)), f)}
  }



  /** Builds the final proof out of an extended Herbrand sequent.
    *
    * For details, see p.5 of "Algorithmic Introduction of Quantified Cuts (Hetzl et al 2013)".
    */
  def buildFinalProof(ehs: GeneralizedExtendedHerbrandSequent) : Option[LKProof] = {

    val endSequent = ehs.endSequent
    val cutFormula = sanitizeVars(ehs.cutFormula)
    val grammar = ehs.grammar
    val flatterms = grammar.flatterms
    
    //Instantiate the cut formula with α_0,...,α_n-1, where n is the number of alphas in the ehs's grammar.
    //partialCutLeft.last ist the all-quantified cut formula, partialCutLeft.head ist the cut formula, with its
    //whole initial quantifier block instantiated to α_0,...,α_n-1.
    val alphas = createFOLVars("α", ehs.grammar.numVars)

    trace("grammar (u,S): ")
    trace(ehs.grammar.u.toString)
    trace(ehs.grammar.s.toString)
    trace("alphas: " + alphas)
    //val partialCutLeft = (0 to alphas.length).toList.reverse.map(n => instantiateFirstN(cutFormula,alphas,n)).toList
    val cutLeft = cutFormula.instantiateAll(alphas)

    trace("cutLeft = " + cutLeft)

    //Fully instantiate the cut formula with s[j=1...n][i] for all i.
    val cutRight = grammar.s.transpose.foldRight(List[FOLFormula]()) { case (t, acc) =>
      (t.foldLeft(cutFormula){case (f, sval) => f.instantiate(sval)}) :: acc
    }

    //leftBranch and rightBranch correspond to the left and right branches of the proof in the middle of
    //p. 5; untilCut merges these together with a cut.

    //trace( "calling solvePropositional" )
    //solvePropositional need only be called with the non-instantiated cutLeft (with the quantifier block in front)
    trace("===FSEQUENT===")
    trace("ehs.antecedent: " + ehs.antecedent)
    trace("ehs.antecedent_alpha: " + ehs.antecedent_alpha)
    trace("cutFormula: " + cutFormula)
    trace("   instatiated with alphas: " + alphas)
    trace("   resulting in cutLeft: " + cutLeft)
    trace("ehs.succedent: " + ehs.succedent)
    trace("ehs.succedent_alpha: " + ehs.succedent_alpha)
    trace(FSequent((ehs.antecedent ++ ehs.antecedent_alpha), (cutLeft +: (ehs.succedent ++ ehs.succedent_alpha))).toString())

    val proofLeft = solvePropositional(FSequent((ehs.antecedent ++ ehs.antecedent_alpha), (cutLeft +: (ehs.succedent ++ ehs.succedent_alpha))))
    val leftBranch = proofLeft match {
      case Some(proofLeft1) => 
        val s1 = uPart(grammar.u.filter(t => !t.freeVariables.intersect(grammar.eigenvariables.toSet).isEmpty), proofLeft1, flatterms)

        trace("=======================")
        trace("s1:")
        trace(s1.toString())
        trace("=======================")
        trace("CF: " + cutFormula)
        trace("alphas: " + alphas)

        //Add sequents to all-quantify the cut formula in the right part of s1
        ForallRightBlock(s1, cutFormula, alphas)

      case None => throw new CutIntroEHSUnprovableException("ERROR: propositional part is not provable.")
    }

    val proofRight = solvePropositional(FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
    val rightBranch = proofRight match {
      case Some(proofRight1) => sPart(cutFormula, grammar.s, proofRight1)
      case None => throw new CutIntroEHSUnprovableException("ERROR: propositional part is not provable: " + FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
    }
    //trace( "done calling solvePropositional" )

    //Merge the left and right branches with a cut.
    val untilCut = CutRule(leftBranch, rightBranch, cutFormula)


    // Contracting the formulas that go to both branches of the cut
    val contractAnt = ehs.antecedent.foldRight(untilCut.asInstanceOf[LKProof]) { case (f, premise) => ContractionLeftRule(premise, f) }
    val contractSucc = ehs.succedent.foldRight(contractAnt.asInstanceOf[LKProof]) { case (f, premise) => ContractionRightRule(premise, f) }

    // Instantiating constant terms from U
    val finalProof = uPart(grammar.u.filter(t => t.freeVariables.intersect(grammar.eigenvariables.toSet).isEmpty), contractSucc, flatterms)

    //trace( "cleaning structural rules" )
    val r = Some(CleanStructuralRules(finalProof))
    //trace( "done cleaning structural rules" )

    r
  }

  // Both methods bellow are responsible for generating the instances of 
  // end-sequent ancestors with the terms from the set U
  def genWeakQuantRules(f: FOLFormula, lst: List[FOLTerm], ax: LKProof) : LKProof = (f, lst) match {
    case (_, Nil) => ax
    case (AllVar(_,_), h::t) => 
      val newForm = f.instantiate(h)
      ForallLeftRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
    case (ExVar(_,_), h::t) =>
      val newForm = f.instantiate(h)
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
    * and the terms are [[a],[b]],
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

    s.transpose.foldLeft(p) { case (p,t) =>

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
    //val sanitizedVars = List[(String,String)](("x","x_0"),("y","x_1"),("z","x_2"),("u","x_3"),("v","x_4"),("w","x_5")).map(
    //  v => (FOLVar(new VariableStringSymbol(v._1)),FOLVar(new VariableStringSymbol(v._2))) )

    //sanitizedVars.foldLeft(f){(f, v) => f match {
    //  case AllVar(_, _) => replaceLeftmostBoundOccurenceOf(v._2, v._1,f)._2
    //  case _ => f
    //}}
    f
  }
}

