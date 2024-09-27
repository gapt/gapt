package gapt.expr.subst

import gapt.expr.ClosedUnderSub
import gapt.proofs.Sequent

import scala.annotation.implicitNotFound

/**
 * Trait that describes the following relation between types `S`, `T`, `U`: If a substitution of type `S` is applied
 * to an element of type `T`, the result will have type `U`.
 *
 * @tparam S A subtype of Substitution.
 * @tparam T The input type.
 * @tparam U The output type.
 */
@implicitNotFound("Cannot apply substituion of type ${S} to type ${T} with result ${U}.")
trait Substitutable[-S <: Substitution, -T, +U] {

  /**
   * Applies a substitution to an argument.
   *
   * @param sub The substitution.
   * @param arg The argument.
   * @return The result.
   */
  def applySubstitution(sub: S, arg: T): U
}

object Substitutable extends ExprSubstitutable7 with SeqSubstitutable {

  /**
   * Testifies that a Set of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableSet[S <: Substitution, T, U](implicit ev: Substitutable[S, T, U]): Substitutable[S, Set[T], Set[U]] =
    (sub, set) => set.map(ev.applySubstitution(sub, _))

  implicit def vectorSubstitutable[S <: Substitution, T, U](implicit ev: Substitutable[S, T, U]): Substitutable[S, Vector[T], Vector[U]] =
    (sub, vec) => vec.map(ev.applySubstitution(sub, _))

  implicit def listSubstitutable[S <: Substitution, T, U](implicit ev: Substitutable[S, T, U]): Substitutable[S, List[T], List[U]] =
    (sub, vec) => vec.map(ev.applySubstitution(sub, _))

  /**
   * Testifies that an Option of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableOption[S <: Substitution, T, U](implicit ev: Substitutable[S, T, U]): Substitutable[S, Option[T], Option[U]] =
    (sub, opt) => opt map { ev.applySubstitution(sub, _) }

  /**
   * Testifies that a Sequent of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableSequent[S <: Substitution, T, U](implicit ev: Substitutable[S, T, U]): Substitutable[S, Sequent[T], Sequent[U]] =
    (sub, sequent) => sequent map { ev.applySubstitution(sub, _) }

  implicit val substitutableString: ClosedUnderSub[String] = (_, str) => str

  /**
   * Testifies that a pair of substitutable objects is substitutable (by applying the substitution to each element).
   */
  implicit def SubstitutablePair[S <: Substitution, T1, U1, T2, U2](
      implicit
      ev1: Substitutable[S, T1, U1],
      ev2: Substitutable[S, T2, U2]
  ): Substitutable[S, (T1, T2), (U1, U2)] =
    (sub, pair) => (ev1.applySubstitution(sub, pair._1), ev2.applySubstitution(sub, pair._2))

}
