package gapt.proofs.context.facet

import scala.reflect.ClassTag

/** Type class for a facet of a context. */
trait Facet[T] {
  def clazz: Class[T]
  def initial: T
}
object Facet {
  def apply[T: ClassTag]( initialValue: T ): Facet[T] = {
    val clazz_ = implicitly[ClassTag[T]].runtimeClass.asInstanceOf[Class[T]]
    new Facet[T] {
      def initial = initialValue

      def clazz = clazz_

      override def toString = clazz.getSimpleName
    }
  }
}