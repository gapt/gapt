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

  implicit object SubstitutableTy extends ClosedUnderSub[Ty] {
    override def applySubstitution( sub: Substitution, ty: Ty ): Ty = ty match {
      case _ if sub.typeMap.isEmpty => ty
      case ty @ TBase( _ )          => ty
      case in -> out                => applySubstitution( sub, in ) -> applySubstitution( sub, out )
      case v @ TVar( _ )            => sub.typeMap.getOrElse( v, v )
    }
  }

  private def substVar( sub: Substitution, v: Var ): Var =
    if ( sub.typeMap.isEmpty ) v else Var( v.name, SubstitutableTy.applySubstitution( sub, v.exptype ) )

  /**
   * The general method for applying substitutions to lambda expressions.
   *
   * @param sub A substitution.
   * @param t A lambda expression.
   * @return The substituted lambda expression.
   */
  private def applySub( sub: Substitution, t: LambdaExpression ): LambdaExpression = t match {
    case _ if sub.isEmpty => t
    case v: Var           => sub.map.getOrElse( v, substVar( sub, v ) )
    case c @ Const( x, ty ) =>
      if ( sub.typeMap.isEmpty ) c else Const( x, SubstitutableTy.applySubstitution( sub, ty ) )
    case App( a, b )                          => App( applySub( sub, a ), applySub( sub, b ) )
    case Abs( v, _ ) if sub.domain contains v => applySub( Substitution( sub.map - v ), t )
    case Abs( v, s ) if sub.range contains v => // TODO: this check is wrong with type substitutions
      // It is safe to rename the bound variable to any variable that is not in freeVariables(s).
      val newV = rename( v, freeVariables( s ) union sub.range )
      applySub( sub, Abs( newV, applySub( Substitution( v -> newV ), s ) ) )
    case Abs( v, s ) => Abs( substVar( sub, v ), applySub( sub, s ) )
  }

  /**
   * Testifies that a Set of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableSet[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Set[T], Set[U]] =
    ( sub, set ) => set.map( ev.applySubstitution( sub, _ ) )

  /**
   * Testifies that a Seq of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableSeq[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Seq[T], Seq[U]] =
    ( sub, seq ) => seq.map( ev.applySubstitution( sub, _ ) )

  /**
   * Testifies that an Option of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableOption[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Option[T], Option[U]] =
    ( sub, opt ) => opt map { ev.applySubstitution( sub, _ ) }

  /**
   * Testifies that a Sequent of substitutable objects is itself substitutable (by mapping over it).
   */
  implicit def SubstitutableSequent[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Sequent[T], Sequent[U]] =
    ( sub, sequent ) => sequent map { ev.applySubstitution( sub, _ ) }

  /**
   * Testifies that a pair of substitutable objects is substitutable (by applying the substitution to each element).
   */
  implicit def SubstitutablePair[S <: Substitution, T1, U1, T2, U2](
    implicit
    ev1: Substitutable[S, T1, U1],
    ev2: Substitutable[S, T2, U2]
  ): Substitutable[S, ( T1, T2 ), ( U1, U2 )] =
    ( sub, pair ) => ( ev1.applySubstitution( sub, pair._1 ), ev2.applySubstitution( sub, pair._2 ) )

  /**
   * Testifies that type `FOLTerm` is closed under `FOLSub`.
   */
  implicit val FOLTermClosedUnderFOLSub: ClosedUnderFOLSub[FOLTerm] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLTerm]

  /**
   * Testifies that type `FOLAtom` is closed under `FOLSub`.
   */
  implicit val FOLAtomClosedUnderFOLSub: ClosedUnderFOLSub[FOLAtom] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLAtom]

  /**
   * Testifies that applying a FOLSubstitution to a FOLFormula that is not an atom will result in a FOLFormula.
   *
   * @param notAnAtom Testifies that T is not a subtype of FOLAtom.
   */
  implicit def FOLFormulaClosedUnderFOLSub[T <: FOLFormula](
    implicit
    notAnAtom: Not[T <:< FOLAtom]
  ): Substitutable[FOLSubstitution, T, FOLFormula] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLFormula]

  /**
   * Testifies that applying a FOLSubstitution to a FOLExpression that is not a formula or a term will result in a FOLExpression.
   *
   * @param notATerm Testifies that T is not a subtype of FOLTerm.
   * @param notAFormula Testifies that T is not a subtype of FOLFormula.
   */
  implicit def FOLExpressionClosedUnderFOLSub[T <: FOLExpression](
    implicit
    notATerm:    Not[T <:< FOLTerm],
    notAFormula: Not[T <:< FOLFormula]
  ): Substitutable[FOLSubstitution, T, FOLExpression] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLExpression]

  /**
   * Testifies that applying a FOLSubstitution to a HOLFormula that is not a FOLFormula will result in a HOLFormula.
   *
   * @param notAFOLFormula Testifies that T is not a subtype of FOLFormula.
   */
  implicit def HOLFormulaClosedUnderFOLSub[T <: HOLFormula](
    implicit
    notAFOLFormula: Not[T <:< FOLFormula]
  ): Substitutable[FOLSubstitution, T, HOLFormula] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[HOLFormula]

  /**
   * Testifies that applying a non-FOL substitution to a FOLAtom results in a HOLAtom.
   * @param notAFOLSub Testifies that S is not a FOLSubstitution.
   */
  implicit def FOLAtomSubstitutable[S <: Substitution](
    implicit
    notAFOLSub: Not[S <:< FOLSubstitution]
  ): Substitutable[S, FOLAtom, HOLAtom] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[HOLAtom]

  /**
   * Testifies that applying a Substitution that is not a FOLSubstitution to a HOLFormula will result in a HOLFormula.
   *
   * @param notAFOLSub Testifies that S is not a subtype of FOLSubstitution.
   */
  implicit def HOLFormulaClosedUnderSub[S <: Substitution, T <: HOLFormula](
    implicit
    notAFOLSub:  Not[S <:< FOLSubstitution],
    notAFOLAtom: Not[T <:< FOLAtom]
  ): Substitutable[S, T, HOLFormula] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[HOLFormula]

  /**
   * Testifies that applying a Substitution that is not a FOLSubstitution to a FOLExpression will result in a LambdaExpression.
   *
   * @param notAFOLSub Testifies that S is not a subtype of FOLSubstitution.
   */
  implicit def FOLExpressionSubstitutable[S <: Substitution, T <: FOLExpression](
    implicit
    notAFOLSub:  Not[S <:< FOLSubstitution],
    notAFOLAtom: Not[T <:< FOLAtom]
  ): Substitutable[S, T, LambdaExpression] =
    ( sub, t ) => applySub( sub, t )

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
  ): Substitutable[Substitution, T, LambdaExpression] =
    ( sub, t ) => applySub( sub, t )
}