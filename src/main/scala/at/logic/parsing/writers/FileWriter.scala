/*
 * FileWriter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.writers

import at.logic.parsing.OutputExporter

abstract class FileWriter(fileName: String) extends OutputExporter {
  val writer = new java.io.FileWriter(fileName)
  def getOutput = writer
}
