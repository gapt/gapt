/*
 * FileReader.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.readers

import at.logic.parsing.InputParser

abstract class FileReader (fileName: String) extends InputParser {
  def getInput() : java.io.Reader = new java.io.FileReader(fileName)
}

