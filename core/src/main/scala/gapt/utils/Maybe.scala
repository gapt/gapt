package gapt.utils
import Maybe._

sealed trait Maybe[+T] {
  def getOrElse[S >: T](default: => S): S =
    this match {
      case None    => default
      case Some(v) => v
    }
  def map[S](f: T => S): Maybe[S] =
    this match {
      case None    => None
      case Some(v) => Some(f(v))
    }
  def foreach(f: T => Unit): Unit =
    this match {
      case None    =>
      case Some(v) => f(v)
    }
}

trait Maybe0 {
  implicit def ofNone[T]: Maybe[T] = None
}
trait Maybe1 extends Maybe0 {
  implicit def ofSome[T](implicit t: T): Maybe[T] = Some(t)
  implicit def explicitOfSome[T](t: T): Maybe[T] = Some(t)
}
object Maybe extends Maybe1 {
  case object None extends Maybe[Nothing]
  case class Some[+T](value: T) extends Maybe[T]
}
