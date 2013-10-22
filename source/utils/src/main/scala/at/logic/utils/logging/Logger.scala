package at.logic.utils.logging
 
import org.slf4j.LoggerFactory

trait Logger {

  val log = LoggerFactory.getLogger(getClass)

  // Ordered by level of importance.
  // E.g. if the logging level is chosen to be info, info, warn and error
  // messages will be logged as well, but not debug and trace.
  def error(msg: => String) = if (log.isErrorEnabled) log.error(msg)
  def error(msg: => String, e:Throwable) = {if (log.isErrorEnabled) log.error(msg,e); throw e}
  def warn(msg: => String) = if (log.isWarnEnabled) log.warn(msg)
  def warn(msg: => String, e:Throwable) = if (log.isWarnEnabled) log.warn(msg,e)
  def info(msg: => String) = if (log.isInfoEnabled) log.info(msg)
  def debug(msg: => String) = if (log.isDebugEnabled) log.debug(msg)
  def trace(msg: => String) = if (log.isTraceEnabled) log.trace(msg)
}

