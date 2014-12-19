/*
 * PublishingBuffer.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import at.logic.utils.patterns.listeners._

import scala.collection.mutable.{ListBuffer => MListBuffer, Buffer => MBuffer}

case class PublishingBufferEvent[A](ar: AddRemove, elem: A)
sealed abstract class AddRemove
case object Add extends AddRemove
case object Remove extends AddRemove

class PublishingBuffer[A] extends MBuffer[A] with ListenerManager[PublishingBufferEvent[A]] {
  val buffer = new MListBuffer[A]()
  
  def +=(elem: A): this.type = {val ret = buffer += elem; fireEvent(PublishingBufferEvent(Add,elem)); this}
  def +=:(elem: A): this.type = {val ret = buffer.+=:(elem); fireEvent(PublishingBufferEvent(Add,elem)); this}
  def insertAll(n: Int, elems: Traversable[A]): Unit = {buffer.insertAll(n,elems); elems.foreach(e => fireEvent(PublishingBufferEvent(Add,e)))}   
  def iterator: Iterator[A] = buffer.iterator  
  def insertAll(n: Int, iter: Iterable[A]): Unit = {buffer.insertAll(n, iter); iter.foreach(elem => fireEvent(PublishingBufferEvent(Add,elem)))}
  def update(n: Int, newelem: A): Unit = {val oldelem = buffer(n); buffer.update(n, newelem); fireEvent(PublishingBufferEvent(Remove,oldelem)); fireEvent(PublishingBufferEvent(Add,newelem))}
  def remove(n: Int): A = {val ret = buffer.remove(n); fireEvent(PublishingBufferEvent(Remove,ret)); ret}
  def clear: Unit = {buffer.foreach(elem => fireEvent(PublishingBufferEvent(Remove,elem))); buffer.clear}
  def length: Int = buffer.length
  def apply(v1: Int): A = buffer.apply(v1)
}
