package at.logic.utils.logging
 
import org.slf4j.LoggerFactory

trait Logger {
  protected def loggerName = getClass.getName
  protected val log = LoggerFactory.getLogger(loggerName)

  // Ordered by level of importance.
  // E.g. if the logging level is chosen to be info, info, warn and error
  // messages will be logged as well, but not debug and trace.
  protected def error(msg: => String) = if (log.isErrorEnabled) log.error(msg)
  protected def error(msg: => String, e:Throwable) = {if (log.isErrorEnabled) log.error(msg,e); throw e}
  protected def warn(msg: => String) = if (log.isWarnEnabled) log.warn(msg)
  protected def warn(msg: => String, e:Throwable) = if (log.isWarnEnabled) log.warn(msg,e)
  protected def info(msg: => String) = if (log.isInfoEnabled) log.info(msg)
  protected def debug(msg: => String) = if (log.isDebugEnabled) log.debug(msg)
  protected def trace(msg: => String) = if (log.isTraceEnabled) log.trace(msg)
}

