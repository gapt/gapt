/**
 * Cut introduction algorithm
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.substitutions._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.interpolation._
import at.logic.algorithms.resolution._
import at.logic.calculi.expansionTrees.{ExpansionTree, toSequent, quantRulesNumber => quantRulesNumberET}
import at.logic.transformations.herbrandExtraction.extractExpansionTrees

class CutIntroException(msg: String) extends Exception(msg)
class CutIntroUncompressibleException(msg: String) extends CutIntroException(msg)

/**
 * Thrown if Extended Herbrand Sequent is unprovable. In theory this does not happen.
 * In practice it does happen if the method used for searching a proof covers a too
 * weak theory (e.g. no equality) or is not complete.
 **/
class CutIntroEHSUnprovableException(msg: String) extends CutIntroException(msg)

object CutIntroduction {

  def apply(proof: LKProof) : LKProof = apply( extractExpansionTrees( proof ))

  /**
   * cut-introduction algorithm (stable version)
   **/
  def apply(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : LKProof = {
    val endSequent = toSequent(ep)
    println("\nEnd sequent: " + endSequent)
    
    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val termsTuples = TermsExtraction(ep)
    val terms = new FlatTermSet(termsTuples)
    println( "Size of term set: " + terms.termset.size )

    val grammars = ComputeGrammars(terms)

    println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      throw new CutIntroUncompressibleException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    println( "Smallest grammar-size: " + smallest )
    println( "Number of smallest grammars: " + smallestGrammars.length )

    // maps a grammar to a proof and a corresponding extended Herbrand-sequent
    def buildProof(grammar:Grammar) = {

      val cutFormula0 = computeCanonicalSolution(endSequent, grammar)
      val ehs = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      val ehs1 = MinimizeSolution(ehs)

      // TODO Uncomment when fixed.
      // Call interpolant before or after minimization??
      //val interpolant = computeInterpolant(ehs1, grammar.s)
      //val cutFormula = AllVar(xvar, And(conj, interpolant.asInstanceOf[FOLFormula]))
      //val ehs2 = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula)

      val proof = buildProofWithCut(ehs1)
      val final_proof = CleanStructuralRules( proof )
 
      ( final_proof, ehs1 )
    }

    val proofs = smallestGrammars.map(buildProof)

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    println("\nGrammar chosen: {" + ehs.grammar.u + "} o {" + ehs.grammar.s + "}")  
    println("\nMinimized cut formula: " + ehs.cutFormula + "\n")

    smallestProof
  }

  /**
   * Experimental implementation of cut-introduction algorithm
   *
   * @return a pair ( p: LKProof, s: String ) where s is a logging string
   * with quantitative data, see testing/resultsCutIntro/stats.ods ('format' sheet)
   * for details.
   **/
  def applyExp(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : ( LKProof , String )= {
    var log = ""

    var SolutionCTime: Long = 0
    var ProofBuildingCTime: Long = 0
    var CleanStructuralRulesCTime:Long = 0
    
    log += ", " + quantRulesNumberET(ep) // log #qnodes

    val endSequent = toSequent(ep)
    println("\nEnd sequent: " + endSequent)
    
    // generate term set
    val t1 = System.currentTimeMillis
    val termsTuples = TermsExtraction(ep)
    val terms = new FlatTermSet(termsTuples)
    val t2 = System.currentTimeMillis
    log += ", " + (t2 - t1) + ", " + terms.termset.size // log tstime, tssize
    println( "Size of term set: " + terms.termset.size )

    // compute grammars
    val t3 = System.currentTimeMillis
    val eigenvariable = FOLVar(new VariableStringSymbol("α"))
    val deltatable = new DeltaTable(terms.termset, eigenvariable)
    val t4 = System.currentTimeMillis
    val gs = ComputeGrammars.findValidGrammars2(terms.termset, deltatable, eigenvariable)
    val grammars = gs.map{ case g => g.flatterms = terms; g }.sortWith((g1, g2) => g1.size < g2.size )
    val t5 = System.currentTimeMillis
    log += ", " + (t4 - t3) + ", " + (t5 - t4) // log dtgtime, dtrtime

    println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      throw new CutIntroUncompressibleException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    println( "Smallest grammar-size: " + smallest )
    println( "Number of smallest grammars: " + smallestGrammars.length )

    log += ", " + smallest + ", " + smallestGrammars.length // mgsize, #mg

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:Grammar) = {
      val t1 = System.currentTimeMillis
      val cutFormula0 = computeCanonicalSolution(endSequent, grammar)
      val ehs = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      val ehs1 = MinimizeSolution.apply2(ehs)
      val t2 = System.currentTimeMillis
      SolutionCTime += t2 - t1
   
      val proof = buildProofWithCut(ehs1)
      val t3 = System.currentTimeMillis
      ProofBuildingCTime += t3 - t2
      
      val pruned_proof = CleanStructuralRules( proof )
      val t4 = System.currentTimeMillis
      CleanStructuralRulesCTime += t4 - t3

      ( pruned_proof, ehs1 )
    }

    val proofs = smallestGrammars.map(buildProof)

    log += ", " + SolutionCTime + ", " + ProofBuildingCTime + ", " + CleanStructuralRulesCTime // log sctime, pbctime, csrctime

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    println("\nMinimized cut formula: " + ehs.cutFormula + "\n")

    log += ", " + rulesNumber( smallestProof ) + ", " + quantRulesNumber( smallestProof ) // log #infc, #qinfc

    ( smallestProof, log )
  }


  /************************ Helper functions *********************/

  def computeInterpolant(ehs: ExtendedHerbrandSequent, s: List[FOLTerm]) : FOLFormula = {
    
    // A[s_i] forall i
    val asi = s.map( t => FOLSubstitution(ehs.cutFormula, ehs.grammar.eigenvariable, t) )
    val cutConj = And(asi)

    // Negative part
    val gamma = ehs.inst_l
    val delta = ehs.inst_r
    val npart = gamma ++ delta

    // Positive part
    val pi = ehs.prop_l :+ cutConj
    val lambda = ehs.prop_r
    val ppart = pi ++ lambda

    // Proof
    val interpProof = solvePropositional(FSequent(gamma++pi, delta++lambda)).get

    // Getting the formula occurrences...
    val occurrences = interpProof.root.antecedent ++ interpProof.root.succedent
    val npart_occ = occurrences.filter(x => npart.contains(x.formula))
    val ppart_occ = occurrences.filter(x => ppart.contains(x.formula))

    // TODO: the casting for FOLFormula fails.
    ExtractInterpolant(interpProof, npart_occ.toSet, ppart_occ.toSet).asInstanceOf[FOLFormula]
  }

  // seq is not used? What the hell???
  def computeCanonicalSolution(seq: Sequent, g: Grammar) : FOLFormula = {
    val flatterms = g.flatterms

    val xvar = FOLVar(new VariableStringSymbol("x"))
    val xFormulas = g.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val freeVars = term.freeVariables
      // Taking only the terms that contain alpha
      if( freeVars.contains(g.eigenvariable) ) {
        val terms = flatterms.getTermTuple(term)
        val f = flatterms.getFormula(term)
        val xterms = terms.map(e => FOLSubstitution(e, g.eigenvariable, xvar))
        val fsubst = f.instantiateAll(xterms)
        f.instantiateAll(xterms) :: acc
      }
      else acc
    }
 
    AllVar(xvar, And(xFormulas))
  }

  /// build a proof with cut from an extended herbrand sequent
  def buildProofWithCut(ehs: ExtendedHerbrandSequent) : LKProof = {

    val endSequent = ehs.endSequent
    val cutFormula = ehs.cutFormula
    val grammar = ehs.grammar
    val flatterms = grammar.flatterms
    
    val alpha = FOLVar(new VariableStringSymbol("α"))
    val cutLeft = cutFormula.instantiate(alpha)
    val cutRight = grammar.s.foldRight(List[FOLFormula]()) { case (t, acc) =>
      cutFormula.instantiate(t) :: acc
    }

    val proofLeft = solvePropositional(FSequent((ehs.antecedent ++ ehs.antecedent_alpha), (cutLeft +: (ehs.succedent ++ ehs.succedent_alpha))))
    val leftBranch = proofLeft match {
      case Some(proofLeft1) => 
        ForallRightRule(uPart(grammar.u.filter(t => t.freeVariables.contains(grammar.eigenvariable)), proofLeft1, flatterms), cutLeft, cutFormula, alpha)
      case None => throw new CutIntroEHSUnprovableException("ERROR: propositional part is not provable.")
    }

    val proofRight = solvePropositional(FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
    val rightBranch = proofRight match {
      case Some(proofRight1) => sPart(cutFormula, grammar.s, proofRight1)
      case None => throw new CutIntroEHSUnprovableException("ERROR: propositional part is not provable: " + FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
    }

    val untilCut = CutRule(leftBranch, rightBranch, cutFormula)


    // Contracting the formulas that go to both branches of the cut

    val contractAnt = ehs.antecedent.foldRight(untilCut.asInstanceOf[LKProof]) { case (f, premise) =>
      ContractionLeftRule(premise, f)
    }

    val contractSucc = ehs.succedent.foldRight(contractAnt.asInstanceOf[LKProof]) { case (f, premise) =>
      ContractionRightRule(premise, f)
    }

    // Instantiating constant terms from U
    val proof = uPart(grammar.u.filter(t => !t.freeVariables.contains(grammar.eigenvariable)), contractSucc, flatterms)

    proof
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

  def uPart(u: List[FOLTerm], ax: LKProof, flatterms: FlatTermSet) : LKProof = {
    u.foldRight(ax) {
      case (term, ax) => 
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

  // Generates the proof derivation where the cut formula is instantiated with
  // the terms from S
  def sPart(cf: FOLFormula, s: List[FOLTerm], p: LKProof) = {
    var first = true;
    s.foldRight(p) { case (t, p) =>
      if(first) {
        first = false
        val scf = cf.instantiate(t)
        ForallLeftRule(p, scf, cf, t)
      }
      else {
        val scf = cf.instantiate(t)
        ContractionLeftRule(ForallLeftRule(p, scf, cf, t), cf)
      }
    }
  }
}

