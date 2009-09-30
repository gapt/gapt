/** 
 * Description: 
 */

package at.logic.parsing.language.prover9

import at.logic.syntax.language._
import at.logic.syntax.language.fol._
import at.logic.parsing.ParsingException
import scala.util.matching.Regex

trait FOLProver9TermParser extends Prover9TermParser[FOL[TypeA,TermA[TypeA]]] {
  def createVariable(name: String) = Variable(name)
  def createConstant(name: String) = Constant(name)
  def createFunction(sym: String, params: List[TermA[TypeA]]) = {
    try {
      (sym, params) match {
        case ("&", x::y::Nil) => val x1 = x.asInstanceOf[FOLFormula[TermA[OType]]]; val y1 = y.asInstanceOf[FOLFormula[TermA[OType]]]; And(x1,y1)
        case ("forall", x::Nil) => val x1 = x.asInstanceOf[FOLFormula[TermA[OType]]]; Forall(x1)
        case ("|", x::y::Nil) => val x1 = x.asInstanceOf[FOLFormula[TermA[OType]]]; val y1 = y.asInstanceOf[FOLFormula[TermA[OType]]]; Or(x1,y1)
        case ("-", x::Nil) => val x1 = x.asInstanceOf[FOLFormula[TermA[OType]]]; Not(x1) // Nicely it matches only the unary -, the binary will be regarded as function
        case (x, ls) => val ls1 = ls.asInstanceOf[List[FOLTerm[TermA[IType]]]]; if (x.charAt(0).isUpperCase) Atom(x,ls1) else Function(x,ls1) 
      }
    }
    catch {
      case e: Exception => Console.println(e.printStackTrace()); throw new ParsingException("Symbol: " + sym + " with parameters: " + params + " does not match any FOL pattern: " + e.getStackTrace()) 
    }
  }
}
