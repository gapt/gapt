package at.logic.gapt.proofs

import scalaz._
import Scalaz._

package object gaptic extends TacticCommands {

  /**
   * Implementation of the [[scalaz.Monad]] typeclass for Tacticals.
   */
  implicit object TacticalMonad extends Monad[Tactical] {
    def point[A]( a: => A ): Tactical[A] = new Tactical[A] {
      def apply( proofState: ProofState ) = ( a -> proofState ).success
    }

    def bind[A, B]( fa: Tactical[A] )( f: A => Tactical[B] ): Tactical[B] =
      fa flatMap f
  }

  implicit class TacticalOptionOps[T]( option: Option[T] ) {
    def toTactical( errorMsg: String ): Tactical[T] = toTactical( errorMsg, None )
    def toTactical( errorMsg: String, goal: OpenAssumption ): Tactical[T] = toTactical( errorMsg, Some( goal ) )
    def toTactical( errorMsg: String, goal: Option[OpenAssumption] ): Tactical[T] = new Tactical[T] {
      override def apply( proofState: ProofState ) =
        option match {
          case None          => TacticalFailure( this, goal, errorMsg ).failureNel
          case Some( value ) => ( value -> proofState ).success
        }

      override def toString = s"$option.toTactical"
    }
  }
}