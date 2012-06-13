package at.logic.utils.executionModels

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Nov 4, 2010
 * Time: 1:44:00 PM
 * To change this template use File | Settings | File Templates.
 */

import collection.mutable.Queue

package searchAlgorithms {
  trait SearchAlgorithm {
    type T
    protected def init: Unit // called by the algorithm and implemented by some object using it as the object is initialized before the trait
    protected def add(t: T): Unit
    protected def get: Option[T]
  }
  trait BFSAlgorithm extends SearchAlgorithm {
    private val ds: Queue[T] = new Queue[T]()
    init // if the object requires the ds to be already existing, then it will not fail now
    protected def add(conf: T): Unit = ds += conf
    protected def get: Option[T] = {
      val res = ds.headOption
      if (res != None) ds.dequeue
      res
    }
  }
}