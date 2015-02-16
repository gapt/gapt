/**
 * Description:
 */

package at.logic.io.readers

import at.logic.io.InputParser

abstract class StringReader( str: String ) extends InputParser {
  def getInput(): java.io.Reader = new java.io.StringReader( str )
}
