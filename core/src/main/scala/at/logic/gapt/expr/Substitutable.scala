package at.logic.gapt.expr

import at.logic.gapt.proofs.Sequent

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

trait ExprSubstitutable1 {
  implicit object SubstitutableTy extends ClosedUnderSub[Ty] {
    override def applySubstitution( sub: Substitution, ty: Ty ): Ty = ty match {
      case _ if sub.typeMap.isEmpty => ty
      case ty @ TBase( _, Nil )     => ty
      case TBase( n, ps )           => TBase( n, ps.map( applySubstitution( sub, _ ) ) )
      case in -> out                => applySubstitution( sub, in ) -> applySubstitution( sub, out )
      case v @ TVar( _ )            => sub.typeMap.getOrElse( v, v )
    }
  }

  private def substVar( sub: Substitution, v: Var ): Var =
    if ( sub.typeMap.isEmpty ) v else Var( v.name, SubstitutableTy.applySubstitution( sub, v.ty ) )

  /**
   * The general method for applying substitutions to lambda expressions.
   *
   * @param sub A substitution.
   * @param t A lambda expression.
   * @return The substituted lambda expression.
   */
  protected def applySub( sub: Substitution, t: Expr ): Expr = t match {
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

  implicit val ExprClosedUnderSub: ClosedUnderSub[Expr] =
    ( sub, t ) => applySub( sub, t )
}

trait ExprSubstitutable2 extends ExprSubstitutable1 {
  implicit val FormulaClosedUnderSub: ClosedUnderSub[Formula] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[Formula]
}

trait ExprSubstitutable3 extends ExprSubstitutable2 {
  implicit val FOLExpressionClosedUnderFOLSub: ClosedUnderFOLSub[FOLExpression] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLExpression]
}

trait ExprSubstitutable4 extends ExprSubstitutable3 {
  implicit val FOLAtomSubstitutable: Substitutable[Substitution, FOLAtom, Atom] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[Atom]
}

trait ExprSubstitutable5 extends ExprSubstitutable4 {
  implicit val FOLTermClosedUnderFOLSub: ClosedUnderFOLSub[FOLTerm] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLTerm]

  implicit val FOLFormulaClosedUnderFOLSub: ClosedUnderFOLSub[FOLFormula] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLFormula]
}

trait ExprSubstitutable6 extends ExprSubstitutable5 {
  implicit val FOLAtomClosedUnderFOLSub: ClosedUnderFOLSub[FOLAtom] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLAtom]
}

object Substitutable extends ExprSubstitutable6 {
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

}