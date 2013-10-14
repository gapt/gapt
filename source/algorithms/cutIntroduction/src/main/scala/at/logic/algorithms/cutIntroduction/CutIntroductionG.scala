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
import at.logic.calculi.lk.macroRules.ForallLeftBlock
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

object CutIntroductionG extends Logger {


  def applyG(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : LKProof = {
    val endSequent = toSequent(ep)
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(ep)
    applyG_(endSequent, termsTuples)
  }

  def applyG(proof: LKProof) : LKProof = {
    val endSequent = proof.root
    //println("\nEnd sequent: " + endSequent)
    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(proof)
    applyG_(endSequent, termsTuples)
  }

  def applyG_(endSequent: Sequent, termsTuples: Map[FOLFormula, List[List[FOLTerm]]]) : LKProof = {

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val terms = new FlatTermSet(termsTuples)

    println("Terms: \n" + terms)
    println("===============================================================")
    println("Termstuples: \n" + termsTuples)
    println("===============================================================")
    println( "\nTerm set: {" + terms.termset + "}" )
    //println( "Size of term set: " + terms.termset.size )

    var beginTime = System.currentTimeMillis;

    val grammars = ComputeGeneralizedGrammars.apply(terms)

    //debug("Compute grammars time: " + (System.currentTimeMillis - beginTime))

    println( "\nNumber of grammars: " + grammars.length )

    if(grammars.length == 0) {
      println("ERROR CUT-INTRODUCTION: No grammars found. Cannot compress.")
      throw new CutIntroException("\nNo grammars found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
    }

    // Compute the proofs for each of the smallest grammars
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter(g => g.size == smallest)

    println( "Smallest grammar-size: " + smallest )
    println( "Number of smallest grammars: " + smallestGrammars.length )

    println("=============================================================")
    println("" + smallestGrammars.map(x => (x.toString() + "\n")))

    beginTime = System.currentTimeMillis;
    //debug("Improving solution...")

    // Build a proof from each of the smallest grammars
    def buildProof(grammar:GeneralizedGrammar) = {
      //trace( "building proof for grammar " + grammar.toPrettyString )

      val cutFormula0 = computeCanonicalSolutionG(endSequent, grammar)
    
      val ehs = new GeneralizedExtendedHerbrandSequent(endSequent, grammar, cutFormula0)
      ehs.minimizeSolution
      trace ( "building final proof" )
      val proof = buildFinalProof(ehs)
      trace ( "done building final proof" )
      
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
  }

  /** Computes the canonical solution with multiple quantifiers from a generalized grammar.
    *
    */
  def computeCanonicalSolutionG(seq: Sequent, g: GeneralizedGrammar) : FOLFormula = {

    val flatterms = g.flatterms

    /** Given a list of eigenvariables, a variable name and a term,
      * returns a list of substitutions that replace ev[i] with the variables "x_i" in term
      * (for 1 <= i <= evs.length).
      */
    def mkFOLSubst(evs: List[FOLVar], varName: String, term: FOLTerm) : List[FOLTerm] = {
      val res = evs.foldLeft((1, List[FOLTerm]())) {(acc, ev) => {
          (acc._1 + 1, FOLSubstitution(term, ev, FOLVar(new VariableStringSymbol(varName + "_" + acc._1))) :: acc._2)
        }}

      res._2
    }

    val varName = "x"

    println("===============================================================")
    println("   g.u:\n")
    println(g.u)
    println("===============================================================")
    println("g.eigenvariables: \n")
    println(g.eigenvariables)
    println("===============================================================")
    println("    g.s:\n")
    println(g.s)
    println("===============================================================")

    val xFormulas = g.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val freeVars = term.freeVariables
      println("   inside g.u.foldRight!   ")
      println("   term.freeVariables: " + freeVars)

      // Taking only the terms that contain alpha
      if( !freeVars.intersect(g.eigenvariables.toSet).isEmpty ) {
        println("      found terms with alphas!")
        val terms = flatterms.getTermTuple(term)
        val f = flatterms.getFormula(term)
        val xterms = terms.flatMap(e => mkFOLSubst(g.eigenvariables, varName, e))
        val fsubst = f.instantiateAll(xterms)
        f.instantiateAll(xterms) :: acc
      }
      else acc
    }
 
    (1 to g.eigenvariables.size).toList.foldLeft(andN(xFormulas)){(f, n) => AllVar(FOLVar(new VariableStringSymbol(varName + "_" + n)), f)}
  }



  /** Builds the final proof out of an extended Herbrand sequent.
    *
    * For details, see p.5 of "Algorithmic Introduction of Quantified Cuts (Hetzl et al 2013)".
    */
  def buildFinalProof(ehs: GeneralizedExtendedHerbrandSequent) : Option[LKProof] = {

    val endSequent = ehs.endSequent
    val cutFormula = ehs.cutFormula
    val grammar = ehs.grammar
    val flatterms = grammar.flatterms
    
    //Instantiate the cut formula with α_1,...,α_n, where n is the number of alphas in the ehs's grammar.
    //partialCutLeft.last ist the all-quantified cut formula, partialCutLeft.head ist the cut formula, with its
    //whole initial quantifier block instantiated to α_1,...,α_n.
    val alphas = createFOLVars("α", ehs.grammar.numVars)

    println("alphas: " + alphas)
    //val partialCutLeft = (0 to alphas.length).toList.reverse.map(n => instantiateFirstN(cutFormula,alphas,n)).toList
    val cutLeft = instantiateFirstN(cutFormula, alphas, alphas.length)

    println("cutLeft = " + cutLeft)

    //Fully instantiate the cut formula with s[j=1...n][i] for all i.
    val cutRight = grammar.s.transpose.foldRight(List[FOLFormula]()) { case (t, acc) =>
      (t.foldLeft(cutFormula){case (f, sval) => f.instantiate(sval)}) :: acc
    }

    //leftBranch and rightBranch correspond to the left and right branches of the proof in the middle of
    //p. 5; untilCut merges these together with a cut.

    //trace( "calling solvePropositional" )
    //solvePropositional need only be called with the non-instantiated cutLeft (with the quantifier block in front)
    println("===FSEQUENT===")
    println(FSequent((ehs.antecedent ++ ehs.antecedent_alpha), (cutLeft +: (ehs.succedent ++ ehs.succedent_alpha))))

    val proofLeft = solvePropositional(FSequent((ehs.antecedent ++ ehs.antecedent_alpha), (cutLeft +: (ehs.succedent ++ ehs.succedent_alpha))))
    val leftBranch = proofLeft match {
      case Some(proofLeft1) => 
        val s1 = uPart(grammar.u.filter(t => !t.freeVariables.intersect(grammar.eigenvariables.toSet).isEmpty), proofLeft1, flatterms)

        //Add sequents to all-quantify the cut formula in the right part of s1, starting with
        //partialCutLeft.head, whith contains only free variables and going to partialCutLeft.last, which has a quantifier block
        //in front instead.
        /*val lPart = alphas.reverse.foldLeft((s1,partialCutLeft)){(acc, ai) =>
                      (ForallLeftRule(acc._1, acc._2.head, acc._2.tail.head, ai), acc._2.tail)
                    }*/
        val lPart = ForallLeftBlock(s1, cutFormula, alphas)
        lPart

        //lPart._1

      case None => throw new CutIntroException("ERROR: propositional part is not provable.")
    }

    val proofRight = solvePropositional(FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
    val rightBranch = proofRight match {
      case Some(proofRight1) => sPart(cutFormula, grammar.s, proofRight1)
      case None => throw new CutIntroException("ERROR: propositional part is not provable: " + FSequent(cutRight ++ ehs.antecedent, ehs.succedent))
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

  /** This... does something.
    *
    */
  def uPart(us: List[types.U], ax: LKProof, flatterms: FlatTermSet) : LKProof = {
    us.foldLeft(ax) {
      case (ax, term) => 
        //Get the arguments of a single u
        val terms = flatterms.getTermTuple(term)
        //Get... uh... flatterms has a hashmap with constant symbols as keys and FOL formulas as
        //values. getFormula returns the value for the key of the function symbol of a single u.
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
      /*val newP = t.reverse.foldLeft((p,pcf)){(acc, singleT) => {
        val p2 = ForallLeftRule(acc._1, acc._2.head, acc._2.tail.head, singleT)
        (p2, acc._2.tail)
        }}*/

      val newP = ForallLeftBlock(p, cf, t)

      //3. If this is not the first time we build cf, 
      //   cf is already present in p and we can do away with its second,
      //   newly generated instance through a contraction rule.
      if (first) {
        first = false
        //newP._1
        newP
      }
      else {
        //ContractionLeftRule(newP._1, cf)
        ContractionLeftRule(newP, cf)
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

