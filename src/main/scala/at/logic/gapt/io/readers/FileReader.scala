/*
 * FileReader.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.io.readers

import at.logic.gapt.io.InputParser

abstract class FileReader( fileName: String ) extends InputParser {
  def getInput(): java.io.Reader = new java.io.FileReader( fileName )
}

