package gapt.utils
import language.higherKinds

/**
 * Unboxed option type similar to `Option[T]`.
 *
 * Note that `USome(UNone()) == UNone()` and `USome(null) == UNone()`.
 */
class UOption[+T](private val t: T) extends AnyVal {
  def isDefined: Boolean = !isEmpty
  def isEmpty: Boolean = t == null
  def unsafeGet: T = t
  def get: T = if (isDefined) unsafeGet else throw new NoSuchElementException
  def getOrElse[S >: T](t: => S): S = if (isDefined) unsafeGet else t
  def map[S](f: T => S): UOption[S] = if (isDefined) USome(f(unsafeGet)) else UNone()
  def flatMap[S](f: T => UOption[S]): UOption[S] = if (isDefined) f(unsafeGet) else UNone()
  def toOption: Option[T] = if (isDefined) Some(unsafeGet) else None
}

object USome {
  def apply[T](t: T): UOption[T] = new UOption(t)
  def unapply[T](t: UOption[T]): UOption[T] = t
}

object UNone {
  def apply[T <: AnyRef](): UOption[T] = new UOption[T](null.asInstanceOf[T])
}
