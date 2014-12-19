package at.logic.utils.logging

import at.logic.utils.dssupport.ListSupport

import scala.collection.mutable
import at.logic.utils.logging.StopwatchStatus.{STOPPED, RUNNING}

/**
 * Stopwatch Status
 */
object StopwatchStatus extends Enumeration {
  type StopwatchStatus = Value
  val RUNNING, STOPPED = Value
}

/**
 * This class defined an object for measuring time and handling errors.
 * Control it with provided functions start, stop, lap, save
 * and read it out by using toXXX methods.
 *
 */
class Stopwatch() extends Logger {

  var status = STOPPED
  var startTime = System.currentTimeMillis()
  var times = mutable.MutableList[(String, Long)]()

  var errorStatus = "OK"

  /**
   * Starts the stopwatch
   */
  def start() = {
    if(status == RUNNING)
    {
      debug("Stopwatch is already running. Resetting it.")
    }
    status = RUNNING
    startTime = System.currentTimeMillis()
  }

  /**
   * Saves the past time since start() or lap()
   * has been called with additional information provided in msg
   * @param msg
   * @return time in milliseconds since last start/lap
   */
  def lap(msg: String) : Long = {
    if(status == STOPPED)
    {
      warn("Stopwatch has not been started. Can not measure time.")
      return 0
    }
    val now = System.currentTimeMillis()
    val diff = (now - startTime)
    times += Tuple2(msg, diff)
    startTime = System.currentTimeMillis()
    diff
  }

  /**
   * Saves the past time since start() or lap() without resetting the time
   * with additional information provided in msg
   * @param msg
   * @return time in milliseconds since last start/lap
   */
  def save(msg: String) : Long = {
    if(status == STOPPED)
    {
      warn("Stopwatch has not been started. Can not measure time.")
      return 0
    }
    val now = System.currentTimeMillis()
    val diff = (now - startTime)
    times += Tuple2(msg, diff)
    diff
  }

  /**
   * Saves the past time since start()
   * has been called with additional information provided in msg
   * Note: In contrast to lap(msg:String), the stopwatch will not be rested to
   * the current time, i.e. further calls of save/lap will be w.r.t. the last start() call
   * @param msg
   * @return time in milliseconds since last start()
   */
  def stop(msg: String) : Long = {
    if(status == STOPPED){
      info("Stopwatch is not running. Nothing to do here.")
      return 0
    }
    val now = System.currentTimeMillis()
    val diff = (now - startTime)
    times += Tuple2(msg, diff)
    diff
  }

  /**
   * Returns the all previously stops/laps in milliseconds
   * @return all times as string
   */
  override def toString() : String = {
    times.toList.foldLeft("")((acc,t) => acc + "\n"+t._1+" @ "+t._2)
  }

  /**
   * Returns the all previously stops/laps as <hours>h <minutes>min <seconds>sec <milliseconds>msec
   * @return all times as string
   */
  def toFormattedString() : String = {
    times.toList.foldLeft("")((acc,t) => acc + "\n"+t._1+" @ "+getHours(t._2)+"h "+getMin(t._2)+"min "+getSec(t._2)+"sec "+getMSec(t._2)+"msec")
  }

  /**
   * Returns the status of the stopwatch
   * @return current status
   */
  def getStatus() : String = {
    if(status == STOPPED){
      return "stopped"
    }
    else
    {
      return "running"
    }
  }

  def getMSec(millisec: Long) : Int = {
    return (millisec % 1000).toInt
  }

  def getSec(millisec: Long) : Int = {
    return ((millisec / 1000) % 60).toInt
  }

  def getMin(millisec: Long) : Int = {
    return (((millisec / 1000) / 60) % 60).toInt
  }

  def getHours(millisec: Long) : Int = {
    return (((millisec / 1000) / 60) / 60).toInt
  }

  /**
   * Returns the all previously stops/laps in xml format
   * @return all times in .xml
   */
  def toXML() : String = {
    times.toList.foldLeft("<times>")((acc,t) => "\n<time name='"+t._1+"'>" +
        "<hours>"+getHours(t._2)+"</hours>"+
        "<minutes>"+getMin(t._2)+"</minutes>"+
        "<seconds>"+getSec(t._2)+"</seconds>"+
        "<milliseconds>"+getMSec(t._2)+"</milliseconds>"+
        "</time>")+
      "</times>"
  }

  /**
   * Returns the all previously stops/laps in csv format
   * @return all times in .csv
   */
  def toCSV() : String = {
    times.toList.foldLeft("")((acc,t) => "\n"+t._1+";"+t._2+";")
  }

}
