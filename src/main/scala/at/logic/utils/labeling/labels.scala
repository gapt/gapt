/*
 * Labels.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.labeling

import reflect.{ClassManifest, Manifest}
 /*
trait Labeled[T] {
  def label: T
} */
// this erasure is really disturbing! */

trait Labeled
{
  type T
  def label: T
  /*def om: Manifest[T]
  def equals[S](a: Any)(implicit m: Manifest[S]) =
    if (om <:< m || m <:< om) {val other = a.asInstanceOf[T]; other == label}
    else if (m == this) {val other = a.asInstanceOf[Labeled]; other.label == label}
    else false  */
  override def hashCode = label.hashCode
  override def toString = label.toString
}

//abstract class LabelKey

//trait MultiLabeled[A] extends Labeled[Map[LabelKey, A]]
