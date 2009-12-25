/** 
 * Description: 
 */

package at.logic.parsing.readers

import at.logic.parsing.InputParser

abstract class StringReader(str: String) extends InputParser {
  def getInput() : java.io.Reader = new java.io.StringReader(str)
}
