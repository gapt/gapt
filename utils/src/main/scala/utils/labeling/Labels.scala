/*
 * Labels.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.labeling

package labels {
  trait Labeled[A] {
    def label: A
  }

  abstract class LabelKey

  trait MultiLabeled[A] extends Labeled[Map[LabelKey, A]]
}
