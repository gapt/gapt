/** 
 * Description: 
 */

package at.logic.parsing

import scala.util.parsing.combinator.RegexParsers

trait InputParser extends RegexParsers {
  def getInput() : java.io.Reader
}
