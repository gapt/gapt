/* Description: An abstract parser for parsing SequentA objects
**/

package at.logic.parsing.calculus
import at.logic.syntax.calculus.SequentA
import at.logic.parsing.InputParser

trait SequentsParser[+T <: SequentA] extends InputParser {
  def sequents: Parser[List[T]]
  def getSequents() : List[T] = {
    val reader = getInput()
    try
    {
      parseAll(sequents, reader).get
    }
    finally
    {
      reader.close();
    }
  }
}

