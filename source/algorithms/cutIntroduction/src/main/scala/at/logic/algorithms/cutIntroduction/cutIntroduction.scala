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
import at.logic.language.lambda.typedLambdaCalculus._
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap

class CutIntroException(msg: String) extends Exception(msg)

object cutIntroduction {

  def apply(proof: LKProof) : LKProof = {

    val endSequent = proof.root

    println("\nEnd sequent: " + endSequent)

    val terms = termsExtraction(proof)

    val quantFormulas = terms.keys.toList.map(fo => fo.formula)

    println("\nQuantified formulas: " + quantFormulas)

    val ant = endSequent.antecedent.map(f => f.formula.asInstanceOf[FOLFormula]).filter(x => !quantFormulas.contains(x))
    val succ = endSequent.succedent.map(f => f.formula.asInstanceOf[FOLFormula]).filter(x => !quantFormulas.contains(x))

    println("\nTerm set: {" + terms + "}")
    println("of size " + terms.size)

    val decompositions = decomposition(terms).sortWith((d1, d2) =>
      (d1._1.foldRight(0) ( (d, acc) => d._2.length + acc)) + d1._2.length
      <
      (d2._1.foldRight(0) ( (d, acc) => d._2.length + acc)) + d2._2.length
    )

    println("\nThe decompositions found were:")
    decompositions.foreach{dec =>
    val l = (dec._1.foldRight(0) ( (d, acc) => d._2.length + acc)) + dec._2.length
      println("{ " + dec._1 + " } o { " + dec._2 + " }  of size " + l)
    }

    val smallestDec = decompositions.head
    // This is a map from formula occurrence to a list of terms
    val u = smallestDec._1
    // This is a list of terms
    val s = smallestDec._2

    println("\nDecomposition chosen: {" + smallestDec._1 + "} o {" + smallestDec._2 + "}")
    
    def genConjunction(forms: List[FOLFormula]) : FOLFormula = forms match {
      case Nil => throw new CutIntroException("The set S of the decomposition should not be empty.")
      case f :: Nil => f
      case f :: t => And(genConjunction(t), f)
    }

    val x = ConstantStringSymbol("X")
    val alpha = FOLVar(new VariableStringSymbol("α"))
    val xalpha = Atom(x, alpha::Nil)

    // X[s_i] forall i
    val xs = s.map(t => Atom(x, t::Nil))
    val bigConj = genConjunction(xs)
   
    val impl = Imp(xalpha, bigConj)

/*
    // TODO: maybe these substitution methods should be put somewhere else...
    // Substitutes a term in a quantified formula (using the first quantifier).
    def substitute(f: FOLFormula, t: FOLTerm) = f match {
      case AllVar(v, form) => FOLSubstitution(form, v, t)
      case ExVar(v, form) => FOLSubstitution(form, v, t)
      case _ => throw new CutIntroException("Error in replacing variables.") 
    }

    def substituteAll(f: FOLFormula, lst: List[FOLTerm]) : FOLFormula = {
    lst match {
      case Nil => f
      case h :: t => substituteAll(substitute(f, h), t)
    }
  }
*/
    // Replace the terms from U in the proper formula
    val alphaFormulasL = u.foldRight(List[FOLFormula]()) { case ((f, setU), acc) =>
      f.formula.asInstanceOf[FOLFormula] match {
        case AllVar(_, _) => 
          (for(e <- setU) yield f.formula.asInstanceOf[FOLFormula].substituteAll(e)) ++ acc
        case _ => acc
      }
    }
    val alphaFormulasR = u.foldRight(List[FOLFormula]()) { case ((f, setU), acc) =>
      f.formula.asInstanceOf[FOLFormula] match {
        case ExVar(_, _) => 
          (for(e <- setU) yield f.formula.asInstanceOf[FOLFormula].substituteAll(e)) ++ acc
        case _ => acc
      }
    }

    val xvar = FOLVar(new VariableStringSymbol("x"))
    val ux = u.map{ 
      case (f, lstterms) => 
        (f, for(t <- lstterms) yield t.map(e => FOLSubstitution(e, alpha, xvar))) 
    }
    
    val xFormulas = ux.foldRight(List[FOLFormula]()) { case ((f, setU), acc) =>
      (for(e <- setU) yield f.formula.asInstanceOf[FOLFormula].substituteAll(e)) ++ acc
    }

    val ehsant = (impl :: alphaFormulasL) ++ ant
    val ehssucc = alphaFormulasR ++ succ

    val conj = genConjunction(xFormulas)

    println("\nExtended Herbrand sequent: \n" + ehsant + " |- " + ehssucc)
    // FIXME: very bad hack for showing the results in order to avoid working
    // with hol and fol formulas at the same time.
    println("\nWhere X is: λx." + conj)

    
    // Building up the final proof with cut
    println("\nGenerating final proof with cut\n")
    
    val cutFormula = AllVar(xvar, conj)
    
    val cutLeft = cutFormula.substitute(alpha)
    val cutRight = s.foldRight(List[FOLFormula]()) { case (t, acc) =>
      cutFormula.substitute(t) :: acc
    }

    // Instantiates all the terms of a quantified formula sequentially
    def genWeakQuantRules(f: FOLFormula, lst: List[FOLTerm], ax: LKProof) : LKProof = (f, lst) match {
      case (_, Nil) => ax
      case(AllVar(_,_), h::t) => 
        val newForm = f.substitute(h)
        ForallLeftRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
      case(ExVar(_,_), h::t) =>
        val newForm = f.substitute(h)
        ExistsRightRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
    }

    def uPart(hm: Map[FormulaOccurrence, List[List[FOLTerm]]], ax: LKProof) : LKProof = {
    hm.foldRight(ax) {
      case ((f, setU), ax) => var first = true; 
        f.formula.asInstanceOf[FOLFormula] match { 
          case AllVar(_, _) => setU.foldRight(ax) { case (terms, ax) =>
            if(first) {
              first = false
              genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax)
            }
            else
              ContractionLeftRule(genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax), f.formula.asInstanceOf[FOLFormula])
          }
          case ExVar(_, _) => setU.foldRight(ax) { case (terms, ax) =>
            if(first) {
              first = false
              genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax)
            }
            else
              ContractionRightRule(genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax), f.formula.asInstanceOf[FOLFormula])
          }
        }
      }
    }

    val axiomL = Axiom((alphaFormulasL ++ ant), (cutLeft +: (succ ++ alphaFormulasR)))
    val leftBranch = ForallRightRule(uPart(u, axiomL), cutLeft, cutFormula, alpha)

    def sPart(cf: FOLFormula, s: List[FOLTerm], ax: LKProof) = {
    var first = true;
    s.foldRight(ax) { case (t, ax) =>
      if(first) {
        first = false
        val scf = cf.substitute(t)
        ForallLeftRule(ax, scf, cf, t)
      }
      else {
        val scf = cf.substitute(t)
        ContractionLeftRule(ForallLeftRule(ax, scf, cf, t), cf)
      }
    }
    }

    val axiomR = Axiom((cutRight ++ alphaFormulasL ++ ant), (succ ++ alphaFormulasR))
    val rightBranch = uPart(u, sPart(cutFormula, s, axiomR))

    val untilCut = CutRule(leftBranch, rightBranch, cutFormula)

    // Contracting the end sequent formulas that were duplicated to be splitted 
    // at the cut rule

    val contractAnt = endSequent.antecedent.foldRight(untilCut.asInstanceOf[LKProof]) { case (f, premise) =>
      ContractionLeftRule(premise, f.formula.asInstanceOf[FOLFormula])
    }

    endSequent.succedent.foldRight(contractAnt.asInstanceOf[LKProof]) { case (f, premise) =>
      ContractionRightRule(premise, f.formula.asInstanceOf[FOLFormula])
    }
  }
}

