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
  def =^(o: Occurrence) = this == o //  should be address equal
}