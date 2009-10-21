/** 
 * Description: Interface for parsing one term 
 */

package at.logic.parsing.language

import at.logic.parsing.InputParser
import at.logic.syntax.language._
import scala.util.parsing.combinator.RegexParsers

trait TermParser[+T <: TermA[TypeA]] extends InputParser {
  def term : Parser[T]
  def getTerm() : T = {
    val reader = getInput()
    try
    {
      parseAll(term, reader).get
    }
    finally
    {
      reader.close();
    }
  }
}
