package gapt.utils

/* Allows to tag an exception with additional debugging data. It could be used as follows:

   if (isBad( element ) ) throw new Exception with ExceptionTag[Element] { tag = element }

   and be used in a try pattern match on the command-line.
 */
trait ExceptionTag[T] {
  val tag: T
}
