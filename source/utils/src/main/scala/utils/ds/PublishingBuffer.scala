/*
 * PublishingBuffer.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import at.logic.utils.patterns.listeners._

import scala.collection.mutable.{Buffer, ListBuffer}

case class PublishingBufferEvent[A](ar: AddRemove, elem: A)
sealed abstract class AddRemove
case object Add extends AddRemove
case object Remove extends AddRemove

class PublishingBuffer[A] extends Buffer[A] with ListenerManager[PublishingBufferEvent[A]] {
  val buffer = new ListBuffer[A]()
  
  def +=(elem: A): Unit = {buffer += elem; fireEvent(PublishingBufferEvent(Add,elem))}
  def +:(elem: A): Buffer[A] = {val ret = buffer.+:(elem); fireEvent(PublishingBufferEvent(Add,elem)); ret}
  def readOnly: Seq[A] = buffer.readOnly
  def insertAll(n: Int, iter: Iterable[A]): Unit = {buffer.insertAll(n, iter); iter.foreach(elem => fireEvent(PublishingBufferEvent(Add,elem)))}
  def update(n: Int, newelem: A): Unit = {val oldelem = buffer(n); buffer.update(n, newelem); fireEvent(PublishingBufferEvent(Remove,oldelem)); fireEvent(PublishingBufferEvent(Add,newelem))}
  def remove(n: Int): A = {val ret = buffer.remove(n); fireEvent(PublishingBufferEvent(Remove,ret)); ret}
  def clear: Unit = {buffer.foreach(elem => fireEvent(PublishingBufferEvent(Remove,elem))); buffer.clear}
  def length: Int = buffer.length
  def elements: Iterator[A] = buffer.elements
  def apply(v1: Int): A = buffer.apply(v1)
}
