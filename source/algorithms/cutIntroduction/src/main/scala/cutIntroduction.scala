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
import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import scala.collection.Map
import scala.collection.mutable._
import scala.collection.mutable.HashMap

class CutIntroException(msg: String) extends Exception(msg)

object cutIntroduction {

  // This method should return a proof eventually
  //def apply(proof: LKProof) : LKProof = {
  def apply(proof: LKProof) : Unit = {

    val endSequent = proof.root

    println("\nEnd sequent: " + endSequent)

    // In order to deal with more than one formula, terms must be colored on
    // this hashmap
    val terms = termsExtraction(proof)

    val quantFormulas = terms.keys.toList.map(fo => fo.formula)

    println("\nQuantified formulas: " + quantFormulas)

    val termset = terms.foldRight(List[FOLTerm]()) ( (t, acc) => 
      t._2.foldRight(acc) ((lst, ac) =>
        lst ++ ac
      )
    )

    val ant = endSequent.antecedent.map(f => f.formula.asInstanceOf[FOLFormula]).filter(x => !quantFormulas.contains(x))
    val succ = endSequent.succedent.map(f => f.formula.asInstanceOf[FOLFormula]).filter(x => !quantFormulas.contains(x))

    println("\nTerm set: {" + termset + "}")
    println("of size " + termset.length)

    val decompositions = decomposition(termset).sortWith((d1, d2) => 
      d1._1.length + d1._2.length < d2._1.length + d2._2.length
    )

    val smallestDec = decompositions.head
    val u = smallestDec._1
    val s = smallestDec._2

    println("\nThe decompositions found were:")
    decompositions.foreach{dec =>
      val l = dec._1.length + dec._2.length
      println("{ " + dec._1 + " } o { " + dec._2 + " }  of size " + l)
    }

    println("\nDecomposition chosen: {" + smallestDec._1 + "} o {" + smallestDec._2 + "}")
    
    val x = ConstantStringSymbol("X")
    val alpha = FOLVar(new VariableStringSymbol("alpha"))
    val xalpha = Atom(x, alpha::Nil)

    val and = Atom(x, s(0)::Nil)

    val bigConj = s.drop(1).foldRight(and) {case (t, form) =>
      val xt = Atom(x, t::Nil)
      And(form, xt)
    }
    
    val impl = Imp(xalpha, bigConj)

    // Right now, replacing blindly all quantified terms by all terms in U. This
    // should be fixed once the colors are applied.
    val alphaFormulas = quantFormulas.foldRight(List[FOLFormula]()) ( (f, acc) =>
      u.foldRight(acc) ((t, lst) => f match {
        case AllVar(v, form) => 
          // Replace t in f
          val ft = FOLSubstitution(form, v, t)
          ft :: lst
        }
      )
    )

    val xvar = FOLVar(new VariableStringSymbol("x"))
    val ux = u.map(t => FOLSubstitution(t, alpha, xvar))

    val xFormulas = quantFormulas.foldRight(List[FOLFormula]()) ( (f, acc) =>
      ux.foldRight(acc) ((t, lst) => f match {
        case AllVar(v, form) => 
          // Replace t in f
          val ft = FOLSubstitution(form, v, t)
          ft :: lst
        }
      )
    )
    
    val ehsant = (impl +: alphaFormulas.toSeq) ++ ant
    val ehssucc = succ

    val conj0 = xFormulas(0)
    val conj1 = xFormulas.drop(1).foldRight(conj0) {case (f, form) =>
      And(form, f)
    }
    val conj2 = ant.foldRight(conj1) {case (f, form) =>
      And(form, f)
    }
    val conj3 = succ.foldRight(conj2) {case (f, form) =>
      And(form, Neg(f))
    }

    println("\nExtended Herbrand sequent: \n" + ehsant + " |- " + ehssucc)
    println("\nWhere X is: " + conj3)
  }
}

