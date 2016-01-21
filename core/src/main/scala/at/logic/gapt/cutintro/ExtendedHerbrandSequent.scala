/*
 *  Extended Herbrand Sequent implementation
 *
 *  For more details on what this is, see: Towards Algorithmic Cut Introduction
 *  (S. Hetzl, A. Leitsch, D. Weller - LPAR-18, 2012)
 *
 */

package at.logic.gapt.cutintro

import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.expr.hol.{ instantiate, containsQuantifier }
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.expr._

case class ExtendedHerbrandSequent( sehs: SchematicExtendedHerbrandSequent, cutFormulas: Seq[FOLFormula] ) {
  require( cutFormulas.size == sehs.ss.size )
  require( isFOLPrenexSigma1( endSequent ) )

  cutFormulas zip sehs.ss foreach {
    case ( All.Block( vs, f ), ( evs, _ ) ) =>
      require( !containsQuantifier( f ) )
      require( vs.size == evs.size )
  }

  def endSequent = sehs.us map { _._1 }

  /** Purely propositional formulas of the end-sequent. */
  val prop = endSequent filterNot { containsQuantifier( _ ) }

  /** Instances of the quantified formulas in the end-sequent. */
  val inst = for (
    ( u, instances ) <- sehs us; if containsQuantifier( u );
    instance <- instances
  ) yield instantiate( u, instance )

  val cutImplications = for ( ( ( eigenVar, cutImplInst ), cutFormula ) <- sehs.ss zip cutFormulas )
    yield instantiate( cutFormula, eigenVar ) --> And( cutImplInst map { instantiate( cutFormula, _ ) } )

  def getDeep: HOLSequent = cutImplications ++: ( prop ++ inst )

  override def toString = getDeep.toString
}
