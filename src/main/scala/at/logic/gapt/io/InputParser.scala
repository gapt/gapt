/**
 * Description:
 */

package at.logic.gapt.io

import scala.util.parsing.combinator.RegexParsers

trait InputParser extends RegexParsers {
  def getInput(): java.io.Reader
}
