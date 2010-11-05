package at.logic.utils.executionModels

import collection.mutable.Queue
import searchAlgorithms._

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Nov 3, 2010
 * Time: 10:46:25 AM
 * To change this template use File | Settings | File Templates.
 *
 * Defines an interface for non-deterministic execution model represented as an infinite stream.
 */

package ndStream {


  trait Configuration[T] {
    def result: Option[T] // if None then it is a non-terminating node otherwise it is a terminating node
  }

  abstract class NDStream[S /*result type*/](val initial: Configuration[S], val myFun: Configuration[S] => List[Configuration[S]]) extends SearchAlgorithm {
    type T = Configuration[S]
    private val results: Queue[S] = new Queue[S]()
    protected def init: Unit = add(initial)
    
    def next: Option[S] = {
      val res = results.headOption
      if (res != None) {
        results.dequeue
        res
      }
      else {
        val conf = get
        if (conf == None) None
        else {
          val confs: List[Configuration[S]] = myFun(conf.get)
          confs.foreach(x => if (x.result == None) add(x) else results.enqueue(x.result.get))
          next
        }
      }
    }
  }
}