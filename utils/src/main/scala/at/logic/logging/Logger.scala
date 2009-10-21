package at.logic.logging

import org.slf4j.LoggerFactory

trait Logging {

  val log = LoggerFactory.getLogger(getClass)

  def debug(msg: => String) = if (log.isDebugEnabled) log.debug(msg)
  def info(msg: => String) = if (log.isInfoEnabled) log.info(msg)
  def error(msg: => String, e:Throwable) = if (log.isErrorEnabled) log.error(msg,e)

}