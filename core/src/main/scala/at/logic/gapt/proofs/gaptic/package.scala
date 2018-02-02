package at.logic.gapt.proofs

import cats.Monad

import scala.annotation.tailrec
import scala.util.{ Left, Right }

package object gaptic extends TacticCommands {

  /**
   * Implementation of the [[cats.Monad]] typeclass for tactics.
   */
  implicit object TacticMonad extends Monad[Tactic] {
    override def pure[A]( x: A ): Tactic[A] = Tactic.pure( x )

    override def flatMap[A, B]( fa: Tactic[A] )( f: ( A ) => Tactic[B] ): Tactic[B] =
      fa.flatMap( f )

    override def tailRecM[A, B]( a: A )( f: ( A ) => Tactic[Either[A, B]] ): Tactic[B] = proofState => {
      @tailrec
      def recurse( a: A, proofState: ProofState ): Either[TacticFailure, ( B, ProofState )] =
        f( a )( proofState ) match {
          case Left( error )                          => Left( error )
          case Right( ( Left( a_ ), proofState_ ) )   => recurse( a_, proofState_ )
          case Right( ( Right( res ), proofState_ ) ) => Right( res -> proofState_ )
        }
      recurse( a, proofState )
    }
  }

  implicit class TacticOptionOps[T]( option: Option[T] ) {
    def toTactic( errorMsg: String ): Tactic[T] = new Tactic[T] {
      override def apply( proofState: ProofState ) =
        option match {
          case None          => Left( TacticFailure( this, proofState, errorMsg ) )
          case Some( value ) => Right( value -> proofState )
        }

      override def toString = s"$option.toTactic"
    }
  }

  implicit class TacticEitherOps[T, E]( either: Either[E, T] ) {
    def toTactic: Tactic[T] = new Tactic[T] {
      override def apply( proofState: ProofState ) =
        either match {
          case Left( error )  => Left( TacticFailure( this, proofState, error.toString ) )
          case Right( value ) => Right( value -> proofState )
        }

      override def toString = s"$either.toTactic"
    }
  }
}
