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

class CutIntroException(msg: String) extends Exception(msg)

object CutIntroduction extends Logger {

  def apply(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : LKProof = {
    val endSequent = toSequent(ep)
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(ep)
    apply_(endSequent, termsTuples)
  }

  def apply(proof: LKProof) : LKProof = {
    val endSequent = proof.root
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(proof)
    apply_(endSequent, termsTuples)
  }

  def apply_(endSequent: Sequent, termsTuples: Map[FOLFormula, List[List[FOLTerm]]]) : LKProof = {

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val terms = new FlatTermSet(termsTuples)

    //println( "\nTerm set: {" + terms.termset + "}" )
    //println( "Size of term set: " + terms.termset.size )

    var beginTime = System.currentTimeMillis;

    val grammars = ComputeGrammars(terms)

    //debug("Compute grammars time: " + (System.currentTimeMillis - beginTime))

    //println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      throw new CutIntroException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    //println( "Smallest grammar-size: " + smallest )
    //println( "Number of smallest grammars: " + smallestGrammars.length )

    beginTime = System.currentTimeMillis;
    //println("Improving solution...")

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:Grammar) = {
      //trace( "building proof for grammar " + grammar.toPrettyString )

      val cutFormula0 = computeCanonicalSolution(endSequent, grammar)
    
      val ehs = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      ehs.minimizeSolution
      //trace ( "building final proof" )
      val proof = buildFinalProof(ehs)
      //trace ( "done building final proof" )
      
      if (proof.isDefined) { Some((proof.get,ehs)) } else { None }
    }

    val proofs = smallestGrammars.map(buildProof).filter(proof => proof.isDefined).map(proof => proof.get)

    //debug("Improve solutions time: " + (System.currentTimeMillis - beginTime))

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    //println("\nGrammar chosen: {" + ehs.grammar.u + "} o {" + ehs.grammar.s + "}")  
    //println("\nMinimized cut formula: " + ehs.cutFormula + "\n")

    smallestProof
      
/* TODO: uncomment when fixed.
    // Computing the interpolant (transform this into a separate function later)
    
    // A[s_i] forall i
    val asi = s.map(t => cutFormula0.substitute(t))
    val cutConj = andN(asi)

    // Negative part
    val gamma = ehs.inst_l
    val delta = ehs.inst_r
    val npart = gamma ++ delta

    // Positive part
    val pi = ehs.prop_l :+ cutConj
    val lambda = ehs.prop_r
    val ppart = pi ++ lambda

    // Proof
    val interpProof = solvePropositional(FSequent(gamma++pi, delta++lambda))

    // Getting the formula occurrences...
    val occurrences = interpProof.root.antecedent ++ interpProof.root.succedent
    val npart_occ = occurrences.filter(x => npart.contains(x.formula))
    val ppart_occ = occurrences.filter(x => ppart.contains(x.formula))

    val interpolant = ExtractInterpolant(interpProof, npart_occ.toSet, ppart_occ.toSet)

    println("Interpolant: " + interpolant.toPrettyString + "\n")

    // Adding interpolant to cut formula
    // TODO: casting does not work here.
    val cutFormula = AllVar(xvar, And(conj, interpolant.asInstanceOf[FOLFormula]))
*/
  }

  // Uses findValidGrammar2 and minimizeSolution2
  
  def apply2(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : LKProof = {
    val endSequent = toSequent(ep)
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(ep)
    apply2_(endSequent, termsTuples)
  }

  def apply2(proof: LKProof) : LKProof = {
    val endSequent = proof.root
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(proof)
    apply2_(endSequent, termsTuples)
  }

  def apply2_(endSequent: Sequent, termsTuples: Map[FOLFormula, List[List[FOLTerm]]]) : LKProof = {

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val terms = new FlatTermSet(termsTuples)

    //println( "\nTerm set: {" + terms.termset + "}" )
    //println( "Size of term set: " + terms.termset.size )

    var beginTime = System.currentTimeMillis;

    val grammars = ComputeGrammars.apply2(terms)

    //debug("Compute grammars time: " + (System.currentTimeMillis - beginTime))

    //println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      println("ERROR CUT-INTRODUCTION: No grammars found. Cannot compress.")
      throw new CutIntroException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    //println( "Smallest grammar-size: " + smallest )
    //println( "Number of smallest grammars: " + smallestGrammars.length )

    //debug("=============================================================")
    //debug("" + smallestGrammars.map(x => (x.toString() + "\n")))

    beginTime = System.currentTimeMillis;
    //debug("Improving solution...")

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:Grammar) = {
      //trace( "building proof for grammar " + grammar.toPrettyString )

      val cutFormula0 = computeCanonicalSolution(endSequent, grammar)
    
      val ehs = new ExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      ehs.minimizeSolution
      //trace ( "building final proof" )
      val proof = buildFinalProof(ehs)
      //trace ( "done building final proof" )
      
      if (proof.isDefined) { Some((proof.get,ehs)) } else { None }
    }

    val proofs = smallestGrammars.map(buildProof).filter(proof => proof.isDefined).map(proof => proof.get)

    //debug("Improve solutions time: " + (System.currentTimeMillis - beginTime))

    // Sort the list by size of proofs
    val sorted = proofs.sortWith((p1, p2) => rulesNumber(p1._1) < rulesNumber(p2._1))

    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    //println("\nGrammar chosen: {" + ehs.grammar.u + "} o {" + ehs.grammar.s + "}")  
    //println("\nMinimized cut formula: " + ehs.cutFormula + "\n")

    smallestProof
      
/* TODO: uncomment when fixed.
    // Computing the interpolant (transform this into a separate function later)
    
    // A[s_i] forall i
    val asi = s.map(t => cutFormula0.substitute(t))
    val cutConj = andN(asi)

    // Negative part
    val gamma = ehs.inst_l
    val delta = ehs.inst_r
    val npart = gamma ++ delta

    // Positive part
    val pi = ehs.prop_l :+ cutConj
    val lambda = ehs.prop_r
    val ppart = pi ++ lambda

    // Proof
    val interpProof = solvePropositional(FSequent(gamma++pi, delta++lambda))

    // Getting the formula occurrences...
    val occurrences = interpProof.root.antecedent ++ interpProof.root.succedent
    val npart_occ = occurrences.filter(x => npart.contains(x.formula))
    val ppart_occ = occurrences.filter(x => ppart.contains(x.formula))

    val interpolant = ExtractInterpolant(interpProof, npart_occ.toSet, ppart_occ.toSet)

    println("Interpolant: " + interpolant.toPrettyString + "\n")

    // Adding interpolant to cut formula
    // TODO: casting does not work here.
    val cutFormula = AllVar(xvar, And(conj, interpolant.asInstanceOf[FOLFormula]))
*/
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
 
    AllVar(xvar, andN(xFormulas))
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

    //trace( "calling solvePropositional" )
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
    //trace( "done calling solvePropositional" )

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

  //------------------------ FORGETFUL RESOLUTION -------------------------//

  class MyFClause[A](val neg: List[A], val pos: List[A])
 
  def toMyFClause(c: FClause) = {
    val neg = c.neg.toList.map(x => x.asInstanceOf[FOLFormula])
    val pos = c.pos.toList.map(x => x.asInstanceOf[FOLFormula])
    new MyFClause[FOLFormula](neg, pos)
  }

  // We assume f is in CNF. Maybe it works also for f not
  // in CNF (since CNFp transforms f to CNF?).
  //
  // Implements forgetful resolution.
  def ForgetfulResolve(f: FOLFormula) : List[FOLFormula] =
  {
    val clauses = CNFp(f).map(c => toMyFClause(c))
    clauses.foldLeft(List[FOLFormula]())( (list, c1) => 
      list ::: clauses.dropWhile( _ != c1).foldLeft(List[FOLFormula]())( (list2, c2) => 
        if (resolvable(c1, c2))
          CNFtoFormula( (clauses.filterNot(c => c == c1 || c == c2 ) + resolve(c1, c2)).toList )::list2
        else
          list2
      )
    )
  }

  /** Converts a CNF back into a FOL formula.
    */
  def CNFtoFormula( cls : List[MyFClause[FOLFormula]] ) : FOLFormula =
  {
    val nonEmptyClauses = cls.filter(c => c.neg.length > 0 || c.pos.length > 0).toList

    if (nonEmptyClauses.length == 0) { TopC }
    else { andN(nonEmptyClauses.map( c => orN(c.pos ++ c.neg.map( l => Neg(l) )) )) }
  }

  /** Converts a numbered CNF back into a FOL formula.
    */
  def NumberedCNFtoFormula( cls : List[MyFClause[(FOLFormula, Int)]] ) : FOLFormula = {
    val nonEmptyClauses = cls.filter(c => c.neg.length > 0 || c.pos.length > 0).toList

    if (nonEmptyClauses.length == 0) { TopC }
    else { andN(nonEmptyClauses.map( c => orN(c.pos.map(l => l._1) ++ c.neg.map( l => Neg(l._1) )) )) }
  }

  // Checks if complementary literals exist.
  def resolvable(l: MyFClause[FOLFormula], r: MyFClause[FOLFormula]) =
    l.pos.exists( f => r.neg.contains(f) ) || l.neg.exists(f => r.pos.contains(f))

  // Assumes that resolvable(l, r). Does propositional resolution.
  // TODO: incorporate contraction.
  def resolve(l: MyFClause[FOLFormula], r: MyFClause[FOLFormula]) : MyFClause[FOLFormula] =
  {
    val cl = l.pos.find( f => r.neg.contains(f) )
    if (cl != None)
      //new MyFClause[FOLFormula]( l.neg ++ (r.neg - cl.get) , (l.pos - cl.get) ++ r.pos )
      // Using diff to remove only one copy of cl.get (the - operator is deprecated)
      new MyFClause[FOLFormula]( l.neg ++ ( r.neg.diff(List(cl.get)) ) , ( l.pos.diff(List(cl.get)) ) ++ r.pos )
    else
    {
      val cr = l.neg.find( f => r.pos.contains(f) ).get
      //new MyFClause[FOLFormula]( (l.neg - cr) ++ r.neg, l.pos ++ (r.pos - cr) )
      // Using diff to remove only one copy of cr (the - operator is deprecated)
      new MyFClause[FOLFormula]( ( l.neg.diff(List(cr)) ) ++ r.neg, l.pos ++ ( r.pos.diff(List(cr)) ) )
    }
  }

  /** Given a formula and a pair of indices (i,j), resolves the two clauses which contain i & j.
    * The original two clauses are deleted and the new, merged clauses is added to the formula.
    *
    * The order of the clauses is NOT preserved!
    *
    * @param cls The formula in numbered clause form: each atom is tuple of the atom itself and its index.
    * @param pair The two atom indices indicating the atoms to be resolved.
    * @return The original formula, with the two resolved clauses deleted and the new, resolved clause added.
    */
  def forgetfulResolve(cls: List[MyFClause[(FOLFormula, Int)]], pair:(Int, Int)) : List[MyFClause[(FOLFormula, Int)]] = {

    /** If either component of pair is present in clause, (clause',True)
      * is returned, where clause' is clause, with the occurring atoms deleted.
      * Otherwise, (clause,False) is returned.
      */
    def resolveClause(clause:MyFClause[(FOLFormula, Int)], pair: (Int, Int)) = {
      val neg = clause.neg.filter(a => a._2 != pair._1 && a._2 != pair._2)
      val pos = clause.pos.filter(a => a._2 != pair._1 && a._2 != pair._2)

      (new MyFClause(neg, pos), neg.length != clause.neg.length || pos.length != clause.pos.length)
    }

    val emptyClause = new MyFClause[(FOLFormula, Int)](Nil, Nil)

    def mergeClauses(clauses:List[MyFClause[(FOLFormula, Int)]]) : MyFClause[(FOLFormula, Int)] = {
      clauses.foldLeft(emptyClause)((c1, c2) => new MyFClause(c1.neg ++ c2.neg, c1.pos ++ c2.pos))
    }

    val startVal = (List[MyFClause[(FOLFormula, Int)]](), List[MyFClause[(FOLFormula, Int)]]())

    //Goes through all clauses with fold, trying to delete the atoms given by pair.
    val (f, rest) = cls.foldLeft(startVal)((x:(List[MyFClause[(FOLFormula, Int)]], List[MyFClause[(FOLFormula, Int)]]), clause:MyFClause[(FOLFormula,Int)]) => {
        val (formula, mergingClause) = x
        val (clause2,resolved) = resolveClause(clause, pair)

        //The first clause was resolved => add it to the temporary mergingClause instead of formula.
        if (resolved && mergingClause.length == 0) { (formula, clause2::Nil) }
        //The 2nd clause was resolved => merge the two clauses and add the result to formula.
        else if (resolved) { (mergeClauses(clause2::mergingClause)::formula, Nil) }
        //No clause was resolved => add the clause as is to the formula and continue.
        else {(clause::formula, mergingClause)}
      })

    //If both atoms were part of the same clause, rest is non-empty. In this case, add rest's 1 clause again.
    if (rest.length > 0) { (rest.head)::f } else { f }
  }
  
  //-----------------------------------------------------------------------//

}

