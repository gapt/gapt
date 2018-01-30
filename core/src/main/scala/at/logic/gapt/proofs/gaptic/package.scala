package at.logic.gapt.proofs

import cats.Monad

import scala.annotation.tailrec
import scala.util.{ Left, Right }

package object gaptic extends TacticCommands {

  /**
   * Implementation of the [[cats.Monad]] typeclass for Tacticals.
   */
  implicit object TacticalMonad extends Monad[Tactical] {
    override def pure[A]( x: A ): Tactical[A] = s => Right( x -> s )

    override def flatMap[A, B]( fa: Tactical[A] )( f: ( A ) => Tactical[B] ): Tactical[B] =
      fa.flatMap( f )

    override def tailRecM[A, B]( a: A )( f: ( A ) => Tactical[Either[A, B]] ): Tactical[B] = proofState => {
      @tailrec
      def recurse( a: A, proofState: ProofState ): Either[TacticalFailure, ( B, ProofState )] =
        f( a )( proofState ) match {
          case Left( error )                          => Left( error )
          case Right( ( Left( a_ ), proofState_ ) )   => recurse( a_, proofState_ )
          case Right( ( Right( res ), proofState_ ) ) => Right( res -> proofState_ )
        }
      recurse( a, proofState )
    }
  }

  implicit class TacticalOptionOps[T]( option: Option[T] ) {
    def toTactical( errorMsg: String ): Tactical[T] = new Tactical[T] {
      override def apply( proofState: ProofState ) =
        option match {
          case None          => Left( TacticalFailure( this, proofState, errorMsg ) )
          case Some( value ) => Right( value -> proofState )
        }

      override def toString = s"$option.toTactical"
    }
  }
}
