package at.logic.utils.executionModels

import collection.mutable.Queue

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


trait Configuration {
    def result: Option[AnyRef] // if None then it is a non-terminating node otherwise it is a terminating node
  }

  class NDStream(initial: Configuration, val myFun: Configuration => List[Configuration]) {
    val ds: Queue[Configuration] = new Queue[Configuration]()
    val results: Queue[AnyRef] = new Queue[AnyRef]()
    ds += initial

    def next: Option[AnyRef] = {
      val res = results.headOption
      if (res != None) {
        results.dequeue
        res
      }
      else {
        val conf = ds.headOption
        if (conf == None) None
        else {
          ds.dequeue
          val confs: List[Configuration] = myFun(conf.get)
          confs.foreach(x => if (x.result == None) ds.enqueue(x) else results.enqueue(x))
          next
        }
      }
    }
  }
}