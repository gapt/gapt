package at.logic.gapt.expr

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.utils.Not

import scala.annotation.implicitNotFound

/**
 * Trait that describes the following relation between types `S`, `T`, `U`: If a substitution of type `S` is applied
 * to an element of type `T`, the result will have type `U`.
 *
 * @tparam S A subtype of Substitution.
 * @tparam T The input type.
 * @tparam U The output type.
 */
@implicitNotFound( "Cannot apply substituion of type ${S} to type ${T} with result ${U}." )
trait Substitutable[-S <: Substitution, -T, +U] {
  /**
   * Applies a substitution to an argument.
   *
   * @param sub The substitution.
   * @param arg The argument.
   * @return The result.
   */
  def applySubstitution( sub: S, arg: T ): U
}

object Substitutable {

  /**
   * Creates an instance of the substitutable typeclass from a function.
   * @param applySub How applying a substitution is supposed to work.
   */
  def instance[S <: Substitution, T, U]( applySub: ( S, T ) => U ): Substitutable[S, T, U] = new Substitutable[S, T, U] {
    override def applySubstitution( sub: S, arg: T ): U = applySub( sub, arg )
  }

  /**
   * The general method for applying substitutions to lambda expressions.
   *
   * @param sub A substitution.
   * @param t A lambda expression.
   * @return The substituted lambda expression.
   */
  private def applySub( sub: Substitution, t: LambdaExpression ): LambdaExpression = t match {
    case v: Var                               => sub.map.getOrElse( v, v )
    case c: Const                             => c
    case App( a, b )                          => App( applySub( sub, a ), applySub( sub, b ) )
    case Abs( v, s ) if sub.domain contains v => applySub( Substitution( sub.map - v ), t )
    case Abs( v, s ) if sub.range contains v =>
      // It is safe to rename the bound variable to any variable that is not in freeVariables(s).
      val newV = rename( v, freeVariables( s ) union sub.range )
      applySub( sub, Abs( newV, applySub( Substitution( v -> newV ), s ) ) )
    case Abs( v, s ) => Abs( v, applySub( sub, s ) )
  }

  /**
   * Testifies that a Set of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableSet[S <: Substitution, T, U](
    implicit
    ev: Substitutable[S, T, U]
  ): Substitutable[S, Set[T], Set[U]] = instance { ( sub: S, set: Set[T] ) =>
    set.map( ev.applySubstitution( sub, _ ) )
  }

  /**
   * Testifies that a Seq of substitutable objects is itself substitutable (by mapping over it).
   *
   * @param ev
   * @tparam S
   * @tparam T
   * @tparam U
   * @return
   */
  implicit def SubstitutableSeq[S <: Substitution, T, U](
    implicit
    ev: Substitutable[S, T, U]
  ): Substitutable[S, Seq[T], Seq[U]] = instance { ( sub: S, seq: Seq[T] ) =>
    seq.map( ev.applySubstitution( sub, _ ) )
  }

  /**
   * Testifies that an Option of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableOption[S <: Substitution, T, U](
    implicit
    ev: Substitutable[S, T, U]
  ): Substitutable[S, Option[T], Option[U]] = instance { ( sub: S, opt: Option[T] ) =>
    opt map { ev.applySubstitution( sub, _ ) }
  }

  /**
   * Testifies that a Sequent of substitutable objects is itself substitutable (by mapping over it).
   *
   * @param ev
   * @tparam S
   * @tparam T
   * @tparam U
   * @return
   */
  implicit def SubstitutableSequent[S <: Substitution, T, U](
    implicit
    ev: Substitutable[S, T, U]
  ): Substitutable[S, Sequent[T], Sequent[U]] = instance { ( sub: S, sequent: Sequent[T] ) =>
    sequent map { ev.applySubstitution( sub, _ ) }
  }

  /**
   * Testifies that a pair of substitutable objects is substitutable (by applying the substitution to each element).
   */
  implicit def SubstitutablePair[S <: Substitution, T1, U1, T2, U2](
    implicit
    ev1: Substitutable[S, T1, U1],
    ev2: Substitutable[S, T2, U2]
  ): Substitutable[S, ( T1, T2 ), ( U1, U2 )] = instance { ( sub: S, pair: ( T1, T2 ) ) =>
    ( ev1.applySubstitution( sub, pair._1 ), ev2.applySubstitution( sub, pair._2 ) )
  }

  /**
   * Testifies that type `FOLTerm` is closed under `FOLSub`.
   *
   */
  implicit val FOLTermClosedUnderFOLSub: ClosedUnderFOLSub[FOLTerm] = instance { ( sub: FOLSubstitution, x: FOLTerm ) =>
    applySub( sub, x ).asInstanceOf[FOLTerm]
  }

  /**
   * Testifies that type `FOLAtom` is closed under `FOLSub`.
   *
   */
  implicit val FOLAtomClosedUnderFOLSub: ClosedUnderFOLSub[FOLAtom] = instance { ( sub: FOLSubstitution, x: FOLAtom ) =>
    applySub( sub, x ).asInstanceOf[FOLAtom]
  }

  /**
   * Testifies that applying a FOLSubstitution to a FOLFormula that is not an atom will result in a FOLFormula.
   *
   * @param notAnAtom Testifies that T is not a subtype of FOLAtom.
   * @tparam T
   * @return
   */
  implicit def FOLFormulaClosedUnderFOLSub[T <: FOLFormula](
    implicit
    notAnAtom: Not[T <:< FOLAtom]
  ) = instance { ( sub: FOLSubstitution, x: T ) =>
    applySub( sub, x ).asInstanceOf[FOLFormula]
  }

  /**
   * Testifies that applying a FOLSubstitution to a FOLExpression that is not a formula or a term will result in a FOLExpression.
   *
   * @param notATerm Testifies that T is not a subtype of FOLTerm.
   * @param notAFormula Testifies that T is not a subtype of FOLFormula.
   * @tparam T
   * @return
   */
  implicit def FOLExpressionClosedUnderFOLSub[T <: FOLExpression](
    implicit
    notATerm:    Not[T <:< FOLTerm],
    notAFormula: Not[T <:< FOLFormula]
  ) = instance { ( sub: FOLSubstitution, x: T ) =>
    applySub( sub, x ).asInstanceOf[FOLExpression]
  }

  /**
   * Testifies that applying a FOLSubstitution to a HOLFormula that is not a FOLFormula will result in a HOLFormula.
   *
   * @param notAFOLFormula Testifies that T is not a subtype of FOLFormula.
   * @tparam T
   * @return
   */
  implicit def HOLFormulaClosedUnderFOLSub[T <: HOLFormula](
    implicit
    notAFOLFormula: Not[T <:< FOLFormula]
  ) = instance { ( sub: FOLSubstitution, x: T ) =>
    applySub( sub, x ).asInstanceOf[HOLFormula]
  }

  /**
   * Testifies that applying a non-FOL substitution to a FOLAtom results in a HOLAtom.
   * @param notAFOLSub Testifies that S is not a FOLSubstitution.
   * @tparam S
   * @return
   */
  implicit def FOLAtomSubstitutable[S <: Substitution](
    implicit
    notAFOLSub: Not[S <:< FOLSubstitution]
  ): Substitutable[S, FOLAtom, HOLAtom] = instance { ( sub: S, x: FOLAtom ) =>
    applySub( sub, x ).asInstanceOf[HOLAtom]
  }

  /**
   * Testifies that applying a Substitution that is not a FOLSubstitution to a HOLFormula will result in a HOLFormula.
   *
   * @param notAFOLSub Testifies that S is not a subtype of FOLSubstitution.
   * @tparam S
   * @return
   */
  implicit def HOLFormulaClosedUnderSub[S <: Substitution, T <: HOLFormula](
    implicit
    notAFOLSub:  Not[S <:< FOLSubstitution],
    notAFOLAtom: Not[T <:< FOLAtom]
  ) = instance { ( sub: S, x: T ) =>
    applySub( sub, x ).asInstanceOf[HOLFormula]
  }

  /**
   * Testifies that applying a Substitution that is not a FOLSubstitution to a FOLExpression will result in a LambdaExpression.
   *
   * @param notAFOLSub Testifies that S is not a subtype of FOLSubstitution.
   * @tparam S
   * @return
   */
  implicit def FOLExpressionSubstitutable[S <: Substitution, T <: FOLExpression](
    implicit
    notAFOLSub:  Not[S <:< FOLSubstitution],
    notAFOLAtom: Not[T <:< FOLAtom]
  ) = instance { ( sub: S, t: T ) =>
    applySub( sub, t )
  }

  /**
   * Testifies that applying a Substitution to a LambdaExpression that is not a FOLExpression or a HOLFormula will result in a LambdaExpression.
   *
   * @param notAFOLExpression Testifies that T is not a subtype of FOLExpression.
   * @param notAHOLFormula Testifies that T is not a subtype of HOLFormula.
   * @tparam T
   * @return
   */
  implicit def LambdaExpressionClosedUnderSub[T <: LambdaExpression](
    implicit
    notAFOLExpression: Not[T <:< FOLExpression],
    notAHOLFormula:    Not[T <:< HOLFormula]
  ) = instance { ( sub: Substitution, t: T ) =>
    applySub( sub, t )
  }
}