/** 
 * Description: 
 */

package at.logic.parsing.readers

import at.logic.parsing.InputParser
import scala.xml.Node
import at.logic.parsing.language.xml.XMLParser.XMLNodeParser

abstract class NodeReader(n: Node) extends XMLNodeParser {
  def getInput() : Node = n
}
