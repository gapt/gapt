/*
 * FileReader.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.readers

import at.logic.gapt.formats.InputParser

abstract class FileReader( fileName: String ) extends InputParser {
  def getInput(): java.io.Reader = new java.io.FileReader( fileName )
}

