/*
 * listeners.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 * taken from http://jim-mcbeath.blogspot.com/2009/04/scala-listener-manager.html
 * consult the link for details on usage
 */

package at.logic.utils.patterns

package listeners {
  trait ListenerManager[E] {
    type L = (E) => Unit
    private var listeners: List[L] = Nil
    private var listenersLock = new Object()

    /** True if the listener is already in our list. */
    private def isListener(listener:L) = listeners.exists(_==listener)

    /** Add a listener to our list if it is not already there. */
    def addListener(listener:L) = listenersLock.synchronized {
      if (!isListener(listener))
        listeners = listener :: listeners
    }

    /** Remove a listener from our list.  If not in the list, ignored. */
    def removeListener(listener:L):Unit = listenersLock.synchronized {
      listeners = listeners.filter(_!=listener)
    }

    /** Apply the given closure to all of the listeners in the list. */
    protected def fireEvent(event:E) = listenersLock.synchronized {
      listeners.foreach(_.apply(event))
    }
  }
}
