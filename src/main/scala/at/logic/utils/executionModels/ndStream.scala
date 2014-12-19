package at.logic.utils.executionModels

import collection.mutable
import searchAlgorithms._

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Nov 3, 2010
 * Time: 10:46:25 AM
 * To change this template use File | Settings | File Templates.
 *
 * Defines an interface for non-deterministic execution model represented as an infinite stream of objects Option[S] where S is some class.
 */

package ndStream {

import annotation.tailrec

trait Configuration[S] {
    def result: Option[S]
    def isTerminal: Boolean // terminal nodes are not added to the configuration queue
  }

  abstract class NDStream[S /*result type*/](val initial: Configuration[S], val myFun: Configuration[S] => Iterable[Configuration[S]]) extends SearchAlgorithm {
    type T = Configuration[S]
    private val results: mutable.Queue[S] = new mutable.Queue[S]()
    protected def init: Unit = add(initial)
    @tailrec
    final def next: Option[S] = {
      val res = results.headOption
      if (res != None) {
        results.dequeue
        res
      }
      else {
        val conf = get
        if (conf == None) None
        else {
          val confs: Iterable[Configuration[S]] = myFun(conf.get)
          confs.foreach(x => {if (x.result != None)
                                results.enqueue(x.result.get);
                              if (!x.isTerminal)
                                add(x)
                              }
                        )
          next
        }
      }
    }
  }
}