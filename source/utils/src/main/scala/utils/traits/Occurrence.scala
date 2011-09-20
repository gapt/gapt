package at.logic.utils.traits

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: 8/30/11
 * Time: 4:13 PM
 * To change this template use File | Settings | File Templates.
 */

//objects mixed with occurrence are always pointerwise equal
trait Occurrence {
  override def equals(a: Any): Boolean = a match {
    case o: Occurrence => this eq o
    case _ => false
  }
  // hashcode does not need to be overriden as equals now means the two points to the same
  // address and therefore has the same hashcode.
}