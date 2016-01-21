/*
 * OutputExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats

trait OutputExporter {
  def getOutput: java.io.Writer
  def close = getOutput.close
}
