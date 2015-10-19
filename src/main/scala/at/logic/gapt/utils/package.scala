package at.logic.gapt

package object utils {

  implicit class ResultChecker[T]( t: T ) {
    @inline final def check( f: T => Unit ): T = { f( t ); t }
  }

}
