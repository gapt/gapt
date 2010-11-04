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
    def result: Option[Any] // if None then it is a non-terminating node otherwise it is a terminating node
  }

  abstract class NDStream(val initial: Configuration, val myFun: Configuration => List[Configuration]) {
    private val results: Queue[Any] = new Queue[Any]()
    protected def init = add(initial)

    protected def add(conf: Configuration): Unit
    protected def get: Option[Configuration]
    
    def next: Option[Any] = {
      val res = results.headOption
      if (res != None) {
        results.dequeue
        res
      }
      else {
        val conf = get
        if (conf == None) None
        else {
          val confs: List[Configuration] = myFun(conf.get)
          confs.foreach(x => if (x.result == None) add(x) else results.enqueue(x.result.get))
          next
        }
      }
    }
  }

  class BFSNDStream(initial: Configuration, myFun: Configuration => List[Configuration]) extends NDStream(initial, myFun) {
    private val ds: Queue[Configuration] = new Queue[Configuration]()
    init
    protected def add(conf: Configuration): Unit = ds += conf
    protected def get: Option[Configuration] = {
      val res = ds.headOption
      if (res != None) ds.dequeue
      res
    }
  }
}