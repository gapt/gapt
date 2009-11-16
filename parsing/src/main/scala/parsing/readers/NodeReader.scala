/** 
 * Description: 
 */

package at.logic.parsing.readers

import at.logic.parsing.InputParser
import scala.xml.{XML,Node}
import at.logic.parsing.language.xml.XMLParser.XMLNodeParser

object XMLReaders {
  abstract class NodeReader(n: Node) extends XMLNodeParser {
    def getInput() : Node = n
  }

  abstract class XMLReader( r: java.io.Reader ) extends XMLNodeParser {
    def getInput() : Node = XML.load( r )
  }
}
