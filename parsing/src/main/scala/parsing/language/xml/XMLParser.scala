/** 
 * Description: Parses the CERES XML format version 4.0
 */

package at.logic.parsing.language.xml

import at.logic.syntax.language._
import at.logic.syntax.language.fol._
import at.logic.parsing.ParsingException
import scala.util.matching.Regex
import scala.xml._ 
import at.logic.parsing.readers.NodeReader

object XMLParser {

  trait XMLElemParser {
    def getInput() : scala.xml.Elem
  }

  trait XMLNodeParser {
    def getInput() : scala.xml.Node
  }

  object XMLUtils {
    def filterSpecial(ns: List[Node]) = 
      ns.filter( // filter out special nodes like PCDATA, ...
                 n => n match { case _ : SpecialNode => false 
                                case _ => true
                                } 
               )
  }

  trait XMLFormulaParser[+T <: TermA[TypeA]] extends XMLNodeParser {
    def getFormula() : T = getFormula( getInput() )

    def getFormula(n : Node) : T =
      n match {
        case <constantatomformula>{_*}</constantatomformula>
             => createAtomFormula(n.attribute("symbol").get.first.text,
                                  getChildTerms(n))
        case <conjunctiveformula>{_*}</conjunctiveformula> 
             => createConjunctiveFormula(n.attribute("type").get.first.text,
                                         getChildFormulas(n))
  //      case <quantifiedformula>{_*}</quantifiedformula>
  //           => {
  //                val child = XMLUtils.filterSpecial(n.child.toList)
  //                val variable = ( new NodeReader(child.first) with XMLFOLTermParser).getTerm() )
  //                val form = ( new NodeReader(child.last) with XMLFOLFormulaParser).getFormula() )
  //                createQuantifiedFormula(n.attribute("type").get.first.text,
  //                                        variable.asInstanceOf[VariableA[TypeA]], form)
  //              }
        case _ => throw throw new ParsingException("Could not parse XML: " + n.toString)
      }

    def getChildTerms(n : Node) =
      XMLUtils.filterSpecial(n.child.toList).map( c => (new NodeReader( c ) with XMLFOLTermParser).getTerm() )

    def getChildFormulas(n : Node) =
      XMLUtils.filterSpecial(n.child.toList).map( c => (new NodeReader( c ) with XMLFOLFormulaParser).getFormula() )
    
    protected def createAtomFormula(name: String, params: List[TermA[TypeA]]): T
    protected def createConjunctiveFormula(sym: String, params: List[TermA[TypeA]]): T
  //  protected def createQuantifiedFormula(sym: String, variable: VariableA[TypeA], formula: TermA[TypeA]): T
  }

  trait XMLFOLFormulaParser extends XMLFormulaParser[FOLFormula[TermA[OType]]] {
    def createAtomFormula(name: String, params: List[TermA[TypeA]]) = Atom(name, params.asInstanceOf[List[FOLTerm[TermA[IType]]]])
    def createConjunctiveFormula(sym: String, params: List[TermA[TypeA]]) =
    {
      val formulas = params.asInstanceOf[List[FOLFormula[TermA[OType]]]]
      sym match {
        case "and" if formulas.size == 2 => And(formulas.first, formulas.last)
        case "or" if formulas.size == 2 => Or(formulas.first, formulas.last)
        case "impl" if formulas.size == 2 => Impl(formulas.first, formulas.last)
        case "neg" if formulas.size == 1 => Not(formulas.first)
      }
    }
  //  def createQuantifiedFormula(sym: String, variable: VariableA[TypeA], formula: TermA[TypeA]) =
  //  {
  //    val fol_var = variable.asInstanceOf[Variable]
  //    val fol_form = formula.asInstanceOf[FOLFormula[TermA[OType]]]
  //    Forall(fol_var, fol_form)
  //  }
  }

  trait XMLTermParser[+T <: TermA[TypeA]] extends XMLNodeParser {
    def getTerm() : T = getTerm( getInput() )

    def getTerm(n: Node) : T =
      n match {
        case <variable/> => createVariable(n.attribute("symbol").get.first.text)
        case <constant/> => createConstant(n.attribute("symbol").get.first.text)
        case <function>{ child @ _* }</function> => createFunction(n.attribute("symbol").get.first.text,
                                                                   getTerms(XMLUtils.filterSpecial(child.toList)))
        case _ => throw throw new ParsingException("Could not parse XML: " + n.toString)
      }

      def getTerms(ns: List[Node]) : List[T] = ns.map( n => getTerm( n ) )

    protected def createVariable(name: String): T
    protected def createConstant(name: String): T
    protected def createFunction(sym: String, params: List[TermA[TypeA]]): T
  }

  trait XMLFOLTermParser extends XMLTermParser[FOLTerm[TermA[IType]]] {
    def createVariable(name: String) = Variable(name)
    def createConstant(name: String) = Constant(name)
    def createFunction(sym: String, params: List[TermA[TypeA]]) = Function(sym, params.asInstanceOf[List[FOLTerm[TermA[IType]]]])
  }

}
