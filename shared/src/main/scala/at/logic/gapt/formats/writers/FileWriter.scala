/*
 * FileWriter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.writers

import at.logic.gapt.formats.OutputExporter

abstract class FileWriter( fileName: String ) extends OutputExporter {
  val writer = new java.io.FileWriter( fileName )
  def getOutput = writer
}
