package gapt.proofs.context.facet

import scala.reflect.ClassTag

/**
 * Type class for a facet of a context.
 *
 * A facet collects some kind of information that is relevant
 * to a context. A facet may for example collect all the base types
 * (uninterpreted, struturally inductive, etc.) currently declared in
 * a context.
 */
trait Facet[T] {

  /**
   * @return An initial value for the facet.
   */
  def initial: T

}

object Facet {

  /**
   * Creates a new instance of [ Facet ].
   *
   * @param initialValue The initial value to be used by the instance.
   * @tparam T The type which is to be made an instance of [Facet].
   * @return An instance of [Facet] for the given type `T`.
   */
  def apply[T: ClassTag]( initialValue: T ): Facet[T] = {

    val clazz_ = implicitly[ClassTag[T]].runtimeClass.asInstanceOf[Class[T]]

    new Facet[T] {

      private def clazz = clazz_

      def initial = initialValue

      override def toString = clazz.getSimpleName
    }
  }

}