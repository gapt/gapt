/*
 * Implements the transformation from the tuple of sets (U_1, ..., U_n) into a
 * single set of terms (f_1(t_1_1), ..., f_1(t_k_1), ..., f_n(t_1_1), ...,
 * f_n(t_k_n)).
 *
 * Ok, this deserves a better explanation... When we extract the terms used to
 * instantiate variables in a proof, the termExtraction algorithm returns a map
 * from FormulaOccurrence F to a set with the tuples containing the terms used
 * to instantiate the quantifiers of F. What this method does is to transform
 * this map into a single list of terms, where the tuples of each formula are
 * prefixed with a fresh function symbol "f_i". 
 *
 * Example: 
 *
 * Map:
 * F1 -> [(a,b), (c,d)]
 * F2 -> [(e), (f), (g)]
 *
 * List of terms:
 * [f_1(a,b), f_1(c,d), f_2(e), f_2(f), f_2(g)]
 *
 * */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.immutable.HashMap
import at.logic.language.hol.logicSymbols._

class FlatTermSetException(msg: String) extends Exception(msg)

// TODO: change the name of the class (to what??)
class FlatTermSet(terms: Map[FOLFormula, List[List[FOLTerm]]]) {

  var formulaFunction = new HashMap[String, FOLFormula]
  // TODO: val (formulaFuncion, termset) = code that processes terms
  var termset : List[FOLTerm] = Nil

  terms.foreach{
    case (f, lst) =>
      val functionSymbol = new TupleFunction
      formulaFunction += (functionSymbol.name -> f)
      termset = lst.foldRight(termset) {
        case (tuple, acc) => Function(functionSymbol.name, tuple) :: acc
      }
  }

  def getFormula(t: FOLTerm) = t match {
    case Function(symbol, _) => formulaFunction(symbol.toString)
    case _ => throw new FlatTermSetException("Term is not a function")
  }

  def getTermTuple(t: FOLTerm) = t match {
    case Function(_, tuple) => tuple
    case _ => throw new FlatTermSetException("Term is not a function")
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


