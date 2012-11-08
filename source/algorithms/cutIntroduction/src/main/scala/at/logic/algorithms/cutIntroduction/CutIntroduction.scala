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
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import at.logic.algorithms.lk._
import at.logic.algorithms.shlk._
import at.logic.algorithms.interpolation._

class CutIntroException(msg: String) extends Exception(msg)

object CutIntroduction {

//  val ehs = new ExtendedHerbrandSequent()

  def apply(proof: LKProof) : Option[LKProof] = {

    val endSequent = proof.root
    println("\nEnd sequent: " + endSequent)

    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(proof)

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val flatterms = new FlatTermSet(termsTuples)
    val terms = flatterms.termset
    val formulaFunctionSymbol = flatterms.formulaFunction

    val quantFormulas = termsTuples.keys.toList.map(fo => fo.formula)
    //println("\nQuantified formulas: " + quantFormulas)

    // Propositional part of antecedent and succedent of the end sequent
    val propAnt = endSequent.antecedent.map(f => f.formula.asInstanceOf[FOLFormula]).filter(x => !quantFormulas.contains(x))
    val propSucc = endSequent.succedent.map(f => f.formula.asInstanceOf[FOLFormula]).filter(x => !quantFormulas.contains(x))

    println("\nTerm set: {" + terms + "}")
    println("of size " + terms.size)

    val decompositions = Decomposition(terms).sortWith((d1, d2) =>
      d1._1.length + d1._2.length < d2._1.length + d2._2.length
    )

    println("Number of decompositions in total: " + decompositions.length)

    if(decompositions.length == 0) {
      println("\nNo decompositions found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
      return None
    }

    // TODO: how to choose the best decomposition?
    val smallestDec = decompositions.head
    // This is a map from formula occurrence to a list of terms
    val u = smallestDec._1
    // This is a list of terms
    val s = smallestDec._2

    println("\nDecomposition chosen: {" + smallestDec._1 + "} o {" + smallestDec._2 + "}")

    val x = ConstantStringSymbol("X")
    val alpha = FOLVar(new VariableStringSymbol("α"))
    val xalpha = Atom(x, alpha::Nil)

    // X[s_i] forall i
    val xs = s.map(t => Atom(x, t::Nil))
    val bigConj = conjunction(xs)
   
    val impl = Imp(xalpha, bigConj)

    // TODO: divide into terms with and without alpha?? (Assuming that they all contain alpha)
    // Replace the terms from U in the proper formula
    val uFormulasLeft = u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val terms = flatterms.getTermTuple(term)
      val f = flatterms.getFormula(term)
      f.formula.asInstanceOf[FOLFormula] match {
        case AllVar(_, _) => f.formula.asInstanceOf[FOLFormula].substituteAll(terms) :: acc
        case _ => acc
      }
    }
    val uFormulasRight = u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val terms = flatterms.getTermTuple(term)
      val f = flatterms.getFormula(term)
      f.formula.asInstanceOf[FOLFormula] match {
        case ExVar(_, _) => f.formula.asInstanceOf[FOLFormula].substituteAll(terms) :: acc
        case _ => acc
      }
    }

    val xvar = FOLVar(new VariableStringSymbol("x"))
    val xFormulas = u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val terms = flatterms.getTermTuple(term)
      val f = flatterms.getFormula(term)
      val xterms = terms.map(e => FOLSubstitution(e, alpha, xvar))
      f.formula.asInstanceOf[FOLFormula].substituteAll(xterms) :: acc
    }

    val ehsant = (impl :: uFormulasLeft) ++ propAnt
    val ehssucc = uFormulasRight ++ propSucc

    val conj = conjunction(xFormulas)

    println("\nExtended Herbrand sequent: \n" + ehsant + " |- " + ehssucc)
    // FIXME: very bad hack for showing the results in order to avoid working
    // with hol and fol formulas at the same time.
    println("\nWhere X is: λx." + conj)

    
    // Building up the final proof with cut
    println("\nGenerating final proof with cut...\n")
    
    //val cutFormula0 = AllVar(xvar, conj)
    val cutFormula = AllVar(xvar, conj)

/* TODO: uncomment when fixed.
    // Computing the interpolant (transform this into a separate function later)
    
    // A[s_i] forall i
    val asi = s.map(t => cutFormula0.substitute(t))
    val cutConj = conjunction(asi)

    // Negative part
    val gamma = alphaFormulasL
    val delta = alphaFormulasR
    val npart = gamma ++ delta

    // Positive part
    val pi = propAnt :+ cutConj
    val lambda = propSucc
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

    val cutLeft = cutFormula.substitute(alpha)
    val cutRight = s.foldRight(List[FOLFormula]()) { case (t, acc) =>
      cutFormula.substitute(t) :: acc
    }

    // Instantiates all the terms of a quantified formula sequentially
    def genWeakQuantRules(f: FOLFormula, lst: List[FOLTerm], ax: LKProof) : LKProof = (f, lst) match {
      case (_, Nil) => ax
      case (AllVar(_,_), h::t) => 
        val newForm = f.substitute(h)
        ForallLeftRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
      case (ExVar(_,_), h::t) =>
        val newForm = f.substitute(h)
        ExistsRightRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
    }

    def uPart(u: List[FOLTerm], ax: LKProof) : LKProof = {
      u.foldRight(ax) {
        case (term, ax) => 
          var first = true;
          val terms = flatterms.getTermTuple(term)
          val f = flatterms.getFormula(term)
          f.formula.asInstanceOf[FOLFormula] match { 
            case AllVar(_, _) => //setU.foldRight(ax) { case (terms, ax) =>
              if(first) {
                first = false
                genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax)
              }
              else
                ContractionLeftRule(genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax), f.formula.asInstanceOf[FOLFormula])
            //}
            case ExVar(_, _) => //setU.foldRight(ax) { case (terms, ax) =>
              if(first) {
                first = false
                genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax)
              }
              else
                ContractionRightRule(genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax), f.formula.asInstanceOf[FOLFormula])
            //}
          }
      }
    }

    val proofLeft = solvePropositional(FSequent((uFormulasLeft ++ propAnt), (cutLeft +: (propSucc ++ uFormulasRight))))
    val leftBranch = proofLeft match {
      case Some(proofLeft1) => ForallRightRule(uPart(u, proofLeft1), cutLeft, cutFormula, alpha)
      case None => throw new CutIntroException("ERROR: propositional part is not provable.")
    }

    def sPart(cf: FOLFormula, s: List[FOLTerm], p: LKProof) = {
      var first = true;
      s.foldRight(p) { case (t, p) =>
        if(first) {
          first = false
          val scf = cf.substitute(t)
          ForallLeftRule(p, scf, cf, t)
        }
        else {
          val scf = cf.substitute(t)
          ContractionLeftRule(ForallLeftRule(p, scf, cf, t), cf)
        }
      }
    }

    val proofRight = solvePropositional(FSequent(cutRight ++ propAnt, propSucc))
    val rightBranch = proofRight match {
      case Some(proofRight1) => sPart(cutFormula, s, proofRight1)
      case None => throw new CutIntroException("ERROR: propositional part is not provable.")
    }

    val untilCut = CutRule(leftBranch, rightBranch, cutFormula)

    // Contracting the end sequent formulas that are propositional (they go to
    // both branches when the cut is applied)

    val contractAnt = endSequent.antecedent.foldRight(untilCut.asInstanceOf[LKProof]) { case (f, premise) =>
      if(!f.formula.containsQuantifier) {
        ContractionLeftRule(premise, f.formula.asInstanceOf[FOLFormula])
      }
      else premise
    }

    val finalProof = endSequent.succedent.foldRight(contractAnt.asInstanceOf[LKProof]) { case (f, premise) =>
      if(!f.formula.containsQuantifier) {
        ContractionRightRule(premise, f.formula.asInstanceOf[FOLFormula])
      }
      else premise
    }

    Some(CleanStructuralRules(finalProof))
  }

/*
  // TODO: uncomment and use once resolve is implemented
  // The canonical solution computed already has only the quantified formulas 
  // from the end-sequent (propositional part is ignored).
  def improveCanonicalSolution(sol: FOLFormula) : FOLFormula = {

    // Remove quantifier 
    val (x, f) = sol match {
      case AllVar(x, form) => (x, form)
      case _ => throw new CutIntroException("ERROR: Canonical solution is not quantified.")
    }

    // Transform to conjunctive normal form
    val cnf = f.toCNF

    // Exhaustive search over the resolvents (depth-first search)
    // TODO: implement resolve (takes a formula and returns a list of resolvents
    // of that formula)
    def searchMinSolution(f: FOLFormula) : FOLFormula = ForgetfulResolve(f) match {
      case Nil => f
      case resolvents => 
        val l = resolvents.foldRight(List[FOLFormula]()) (r, acc => 
          // Should I insert this quantifier by hand?
          if(ehs.isValidWith(AllVar(x,r))) {
            searchMinSolution(r) :+ acc
          }
          else acc
        )
        // Return the minimum resolvent
        l.sortWith((r1,r2) => r1.numOfAtoms < r2.numOfAtoms)._1
    }

    searchMinSolution(cnf)
  }
*/
}

