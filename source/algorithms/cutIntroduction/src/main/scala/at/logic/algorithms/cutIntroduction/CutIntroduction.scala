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
import at.logic.utils.logging.Logger

class CutIntroException(msg: String) extends Exception(msg)

// Logging old and new implementations in different files.
object CutIntro1Logger extends Logger
object CutIntro2Logger extends Logger

object CutIntroduction {
  
  // For experiments:
  // Note: collecting data only of proofs that were compressed.
  var totalTime = -1.0
  var termExtractionTime = -1.0
  var deltaTableTime = -1.0
  var grammarComputationTime = -1.0
  var quantRules = -1
  var numRules = -1
  var termSetSize = -1
  var minGrammars = -1
  // This list has the size of the variable minGrammars
  var improvSol_proofBuild = List[(Long, Long)]()
  
  /************************ 1st Cut-Introduction ***************************/

  def apply(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : LKProof = {
   
    improvSol_proofBuild = Nil

    val t0 = System.currentTimeMillis
    quantRules = quantRulesNumberET(ep)

    val endSequent = toSequent(ep)
    println("\nEnd sequent: " + endSequent)
    
    // Extract the terms used to instantiate each formula
    val t1 = System.currentTimeMillis
    val termsTuples = TermsExtraction(ep)
    val t2 = System.currentTimeMillis
    termExtractionTime = t2 - t1

    val finalProof = apply_(endSequent, termsTuples)

    val tn = System.currentTimeMillis
    totalTime = tn - t0
    
    CutIntro1Logger.trace(quantRules + ", " + termSetSize +  ", " + minGrammars + ", "
      + totalTime + ", " + termExtractionTime + ", " + deltaTableTime + ", " + grammarComputationTime + ", "
      + improvSol_proofBuild.foldLeft("")((acc, t) => t._1 + ", " + t._2 + ", " + acc) )

    finalProof
  }

  def apply(proof: LKProof) : LKProof = {
    
    improvSol_proofBuild = Nil

    val t0 = System.currentTimeMillis
    quantRules = quantRulesNumber(proof)
    numRules = rulesNumber(proof)
    
    val endSequent = proof.root
    println("\nEnd sequent: " + endSequent)
    
    // Extract the terms used to instantiate each formula
    val t1 = System.currentTimeMillis
    val termsTuples = TermsExtraction(proof)
    val t2 = System.currentTimeMillis
    termExtractionTime = t2 - t1
    
    val finalProof = apply_(endSequent, termsTuples)
    
    val tn = System.currentTimeMillis
    totalTime = tn - t0
    
    CutIntro1Logger.trace(numRules + ", " + quantRules + ", " + termSetSize +  ", " + minGrammars + ", "
      + totalTime + ", " + termExtractionTime + ", " + deltaTableTime + ", " + grammarComputationTime + ", "
      + improvSol_proofBuild.foldLeft("")((acc, t) => t._1 + ", " + t._2 + ", " + acc) )

    finalProof
  }

  def apply_(endSequent: Sequent, termsTuples: Map[FOLFormula, List[List[FOLTerm]]]) : LKProof = {

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val terms = new FlatTermSet(termsTuples)
    termSetSize = terms.termset.size

    println( "Size of term set: " + terms.termset.size )

    // Building the delta-table
    val eigenvariable = FOLVar(new VariableStringSymbol("α"))
    val t3 = System.currentTimeMillis
    val deltatable = new DeltaTable(terms.termset, eigenvariable)
    val t4 = System.currentTimeMillis
    deltaTableTime = t4 - t3

    val t1 = System.currentTimeMillis
    val grammars = ComputeGrammars.findValidGrammars(terms.termset, deltatable, eigenvariable)
      .sortWith((g1, g2) => g1.size < g2.size )
      .map{ case g => g.flatterms = terms; g }
    val t2 = System.currentTimeMillis
    grammarComputationTime = t2 - t1

    println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      throw new CutIntroException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    println( "Smallest grammar-size: " + smallest )
    println( "Number of smallest grammars: " + smallestGrammars.length )
    minGrammars = smallestGrammars.length

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:Grammar) = {

      val cutFormula0 = computeCanonicalSolution(endSequent, grammar)
      val ehs = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula0)

      val t1 = System.currentTimeMillis
      val ehs1 = MinimizeSolution(ehs)
      val t2 = System.currentTimeMillis
      val improvSol = t2 - t1

      // TODO Uncomment when fixed.
      // Call interpolant before or after minimization??
      //val interpolant = computeInterpolant(ehs1, grammar.s)
      //val cutFormula = AllVar(xvar, And(conj, interpolant.asInstanceOf[FOLFormula]))
      //val ehs2 = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula)

      val t3 = System.currentTimeMillis
      val proof = buildFinalProof(ehs1)
      val t4 = System.currentTimeMillis
      val proofBuild = t4 - t3

      if (proof.isDefined) { 
        improvSol_proofBuild = improvSol_proofBuild :+ (improvSol, proofBuild)
        Some((proof.get,ehs1)) 
      } else { None }
    }

    val proofs = smallestGrammars.map(buildProof).filter(proof => proof.isDefined).map(proof => proof.get)

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    println("\nGrammar chosen: {" + ehs.grammar.u + "} o {" + ehs.grammar.s + "}")  
    println("\nMinimized cut formula: " + ehs.cutFormula + "\n")

    smallestProof
  }

  /************************ 2nd Cut-Introduction ***************************/

  // Uses findValidGrammar2 and minimizeSolution2 (optimized)
 
  def apply2(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : LKProof = {
    
    improvSol_proofBuild = Nil

    val t0 = System.currentTimeMillis
    quantRules = quantRulesNumberET(ep)
    
    val endSequent = toSequent(ep)
    println("\nEnd sequent: " + endSequent)
    
    // Extract the terms used to instantiate each formula
    val t1 = System.currentTimeMillis
    val termsTuples = TermsExtraction(ep)
    val t2 = System.currentTimeMillis
    termExtractionTime = t2 - t1
    
    val finalProof = apply2_(endSequent, termsTuples)

    val tn = System.currentTimeMillis
    totalTime = tn - t0
    
    CutIntro2Logger.trace(quantRules + ", " + termSetSize +  ", " + minGrammars + ", "
      + totalTime + ", " + termExtractionTime + ", " + grammarComputationTime + ", "
      + improvSol_proofBuild.foldLeft("")((acc, t) => t._1 + ", " + t._2 + ", " + acc) )

    finalProof
  }

  def apply2(proof: LKProof) : LKProof = {
    
    improvSol_proofBuild = Nil

    val t0 = System.currentTimeMillis
    quantRules = quantRulesNumber(proof)
    numRules = rulesNumber(proof)
    
    val endSequent = proof.root
    println("\nEnd sequent: " + endSequent)

    // Extract the terms used to instantiate each formula
    val t1 = System.currentTimeMillis
    val termsTuples = TermsExtraction(proof)
    val t2 = System.currentTimeMillis
    termExtractionTime = t2 - t1
    
    val finalProof = apply2_(endSequent, termsTuples)
    
    val tn = System.currentTimeMillis
    totalTime = tn - t0
    
    CutIntro2Logger.trace(numRules + ", " + quantRules + ", " + termSetSize +  ", " + minGrammars + ", "
      + totalTime + ", " + termExtractionTime + ", " + grammarComputationTime + ", "
      + improvSol_proofBuild.foldLeft("")((acc, t) => t._1 + ", " + t._2 + ", " + acc) )

    finalProof
  }

  def apply2_(endSequent: Sequent, termsTuples: Map[FOLFormula, List[List[FOLTerm]]]) : LKProof = {

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val terms = new FlatTermSet(termsTuples)
    termSetSize = terms.termset.size

    println( "Size of term set: " + terms.termset.size )

    // Building the delta-table
    val eigenvariable = FOLVar(new VariableStringSymbol("α"))
    val t3 = System.currentTimeMillis
    val deltatable = new DeltaTable(terms.termset, eigenvariable)
    val t4 = System.currentTimeMillis
    deltaTableTime = t4 - t3

    val t1 = System.currentTimeMillis
    val grammars = ComputeGrammars.findValidGrammars2(terms.termset, deltatable, eigenvariable)
      .sortWith((g1, g2) => g1.size < g2.size )
      .map{ case g => g.flatterms = terms; g }
    val t2 = System.currentTimeMillis
    grammarComputationTime = t2 - t1

    println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      throw new CutIntroException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    println( "Smallest grammar-size: " + smallest )
    println( "Number of smallest grammars: " + smallestGrammars.length )
    minGrammars = smallestGrammars.length

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:Grammar) = {

      val cutFormula0 = computeCanonicalSolution(endSequent, grammar)
      val ehs = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      
      val t1 = System.currentTimeMillis
      val ehs1 = MinimizeSolution.apply2(ehs)
      val t2 = System.currentTimeMillis
      val improvSol = t2 - t1
   
      // TODO Uncomment when fixed.
      // Call interpolant before or after minimization??
      //val interpolant = computeInterpolant(ehs1, grammar.s)
      //val cutFormula = AllVar(xvar, And(conj, interpolant))
      //val ehs2 = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula)
    
      val t3 = System.currentTimeMillis
      val proof = buildFinalProof(ehs1)
      val t4 = System.currentTimeMillis
      val proofBuild = t4 - t3
      
      if (proof.isDefined) { 
        improvSol_proofBuild = improvSol_proofBuild :+ (improvSol, proofBuild)
        Some((proof.get,ehs1)) 
      } else { None }
    }

    val proofs = smallestGrammars.map(buildProof).filter(proof => proof.isDefined).map(proof => proof.get)

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    println("\nMinimized cut formula: " + ehs.cutFormula + "\n")

    smallestProof
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

  def buildFinalProof(ehs: ExtendedHerbrandSequent) : Option[LKProof] = {

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
      case None => throw new CutIntroException("ERROR: propositional part is not provable.")
    }

    val proofRight = solvePropositional(FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
    val rightBranch = proofRight match {
      case Some(proofRight1) => sPart(cutFormula, grammar.s, proofRight1)
      case None => throw new CutIntroException("ERROR: propositional part is not provable: " + FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
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
    val finalProof = uPart(grammar.u.filter(t => !t.freeVariables.contains(grammar.eigenvariable)), contractSucc, flatterms)

    Some(CleanStructuralRules(finalProof))
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

