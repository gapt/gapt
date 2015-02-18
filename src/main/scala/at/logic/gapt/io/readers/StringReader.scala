/**
 * Description:
 */

package at.logic.gapt.io.readers

import at.logic.gapt.io.InputParser

abstract class StringReader( str: String ) extends InputParser {
  def getInput(): java.io.Reader = new java.io.StringReader( str )
}
