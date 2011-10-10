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
 * Defines an interface for non-deterministic execution model represented as an infinite stream of objects Option[S] where S is some class.
 */

package ndStream {


  trait Configuration[S] {
    def result: Option[S]
    def isTerminal: Boolean // terminal nodes are not added to the configuration queue
  }

  abstract class NDStream[S /*result type*/](val initial: Configuration[S], val myFun: Configuration[S] => Iterable[Configuration[S]]) extends SearchAlgorithm {
    type T = Configuration[S]
    private val results: Queue[S] = new Queue[S]()
    protected def init: Unit = add(initial)

    // this is a tail recursion but from some reason scala does not replace it by a loop. TODO: replace it explicitely.
    def next: Option[S] = {
      while (results.headOption == None) {
        val conf = get
        if (conf == None) return None
        else myFun(conf.get).foreach(x => {if (x.result != None) results.enqueue(x.result.get); if (!x.isTerminal) add(x)})
      }

      val res = results.headOption
      results.dequeue
      res
    }
  }
}