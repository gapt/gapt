/**
 * Description:
 */

package at.logic.gapt.formats.readers

import at.logic.gapt.formats.InputParser

abstract class StringReader( str: String ) extends InputParser {
  def getInput(): java.io.Reader = new java.io.StringReader( str )
}
