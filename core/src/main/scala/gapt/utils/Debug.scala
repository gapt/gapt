package gapt.utils

import sourcecode.Line
import sourcecode.FileName

extension [T](inline x: T) {

  /**
  * Pretty-prints out the value and returns it.
  * This is useful for debug printing inside a nested structure
  *
  * @return the value this method is called on
  */
  inline def d: T = ${ dbgImpl('x) }
}

import scala.quoted.*
private def dbgImpl[T: Type](x: Expr[T])(using Quotes): Expr[T] = {
  val code = Expr(x.show)
  '{ pprint.log(sourcecode.Text($x, $code)) }
}
