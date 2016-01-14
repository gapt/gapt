/*
 * StandardClauseSet.scala
 *
 */

package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lkskNew.LKskProof.{ LabelledFormula, LabelledSequent, Label }
import at.logic.gapt.expr._
import at.logic.gapt.utils.logging.Logger
import scala.annotation.tailrec
import scala.util.control.TailCalls._
import at.logic.gapt.proofs.ceres._

object StandardClauseSet extends StandardClauseSet

/**
 * Does not work for Schema, for CERESomega only if all labels are empty (clauses are correct,
 * but labels forgotten).
 */
class StandardClauseSet {
  /**
   * Creates the characteristic sequent set from a struct
   * @param struct The struct to be converted
   * @param contract if contract is set, duplicate formulas will not be added to the clause during a merge (default: true)
   * @return
   */
  def apply( struct: Struct[Label], contract: Boolean = true ): Set[LabelledSequent] = struct match {
    case A( Top(), _ )    => Set()
    case A( Bottom(), _ ) => Set( Sequent( Nil, Nil ) )
    case A( fo, label :: Nil ) =>
      val x: LabelledFormula = ( label, fo )
      Set( Sequent( Nil, List( x ) ) )
    case Dual( A( Top(), _ ) )    => Set( Sequent( Nil, Nil ) )
    case Dual( A( Bottom(), _ ) ) => Set()
    case Dual( A( fo, label :: Nil ) ) =>
      val x: LabelledFormula = ( label, fo )
      Set( Sequent( List( x ), Nil ) )
    case EmptyPlusJunction()            => Set()
    case EmptyTimesJunction()           => Set( Sequent( Nil, Nil ) )
    case Plus( EmptyPlusJunction(), x ) => apply( x )
    case Plus( x, EmptyPlusJunction() ) => apply( x )
    case Plus( A( f1, _ ), Dual( A( f2, _ ) ) ) if f1 == f2 =>
      Set()
    case Plus( Dual( A( f2, _ ) ), A( f1, _ ) ) if f1 == f2 =>
      Set()
    case Plus( x, y ) =>
      apply( x ) ++ apply( y )
    case Times( EmptyTimesJunction(), x, _ ) => apply( x )
    case Times( x, EmptyTimesJunction(), _ ) => apply( x )
    case Times( x, y, _ ) =>
      val xs = apply( x )
      val ys = apply( y )
      xs.flatMap( x1 => ys.flatMap( y1 => {
        if ( contract )
          Set( delta_compose( x1, y1 ) )
        else
          Set( x1 ++ y1 )
      } ) )

    case _ => throw new Exception( "Unhandled case: " + struct )
  }

  /* Like compose, but does not duplicate common terms */
  private def delta_compose( fs1: LabelledSequent, fs2: LabelledSequent ) = Sequent(
    fs1.antecedent ++ fs2.antecedent.diff( fs1.antecedent ),
    fs1.succedent ++ fs2.succedent.diff( fs1.succedent )
  )
}
