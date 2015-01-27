/**
 * Extraction of terms for the cut-introduction algorithm.
 *
 * NOTE: Prenex formulas only.
 *
 * Collects all tuples of terms used to instantiate blocks of quantifiers and
 * stores these tuples in a map. The map associates each formula with the
 * respective tuples used to instantiate its quantifier block.
 * In order to use the term set in the cut-introduction algorithm, the map is
 * transformed into a single list of terms (termset) where the tuples of each
 * formula are prefixed with a fresh function symbol "f_i". This transformation
 * is done by the TermSet class, which stores the new term set and the mapping
 * of fresh function symbols to their respective formulas.
 *
 * Example: 
 *
 * Map:
 * F1 -> [(a,b), (c,d)]
 * F2 -> [(e), (f), (g)]
 *
 * List of terms (termset):
 * [f_1(a,b), f_1(c,d), f_2(e), f_2(f), f_2(g)]
 *
 * Name mapping (formulaFunction):
 * f_1 -> F1
 * f_2 -> F2
 *
 * */

package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.expansionTrees._
import at.logic.calculi.expansionTrees._
import at.logic.calculi.expansionTrees.{MWeakQuantifier , MStrongQuantifier}
import at.logic.calculi.lk.base._
import at.logic.language.fol._
import at.logic.transformations.herbrandExtraction._
import scala.collection.immutable.HashMap

class TermsExtractionException(msg: String) extends Exception(msg)

object TermsExtraction {

  def apply(proof: LKProof) : TermSet = apply(extractExpansionSequent(proof, false))

  def apply(expProof: ExpansionSequent) : TermSet = {
    
    val multiExpTrees = expProof.antecedent.map(et => compressQuantifiers(et)) ++ expProof.succedent.map(et => compressQuantifiers(et))

    val tuple_set = multiExpTrees.foldRight( HashMap[FOLFormula, List[List[FOLTerm]]]() ) {case (mTree, map) =>
      if(isPrenex(mTree.toShallow.asInstanceOf[FOLFormula])) {
        mTree match {
          case MWeakQuantifier(form, children) =>
            val f = form.asInstanceOf[FOLFormula]
            val terms = children.map{ case (tree, termsSeq) => termsSeq.map(t => t.asInstanceOf[FOLTerm]).toList}.toList
            if(map.contains(f) ) {
              val t = map(f)
              map + (f -> (t ++ terms) )
            }
            else map + (f -> terms)
          case MStrongQuantifier(_,_,_) => throw new TermsExtractionException("ERROR: Found strong quantifier while extracting terms.")
          case _ => map
        }
      }
      else throw new TermsExtractionException("ERROR: Trying to extract the terms of an expansion proof with non-prenex formulas.")
    }

    new TermSet (tuple_set)
  }
}

class TermSet (terms: Map[FOLFormula, List[List[FOLTerm]]]){

  var formulaFunction = new HashMap[String, FOLFormula]
  var set : List[FOLTerm] = Nil

  terms.foreach{
    case (f, lst) =>
      val functionSymbol = new TupleFunction
      formulaFunction += (functionSymbol.name -> f)
      set = lst.foldRight(set) {
        case (tuple, acc) => Function(functionSymbol.name, tuple) :: acc
      }
  }

  def getFormula(t: FOLTerm) = t match {
    case Function(symbol, _) => formulaFunction(symbol.toString)
    case _ => throw new TermsExtractionException("Term is not a function: "+t)
  }

  def getTermTuple(t: FOLTerm) = t match {
    case Function(_, tuple) => tuple
    case _ => throw new TermsExtractionException("Term is not a function: "+t)
  }

  object TupleFunction {
    private var current = 0
    private def inc = {
      current += 1
      current
    }
  }
  class TupleFunction {
    val id = TupleFunction.inc
    val name = "tuple" + id
  }
}
