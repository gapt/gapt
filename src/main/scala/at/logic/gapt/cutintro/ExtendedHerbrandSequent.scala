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
  /** Quantified formulas of the end-sequent. */
  val quant = endSequent filter { containsQuantifier( _ ) }

  def prop_l = prop.antecedent
  def prop_r = prop.succedent
  def quant_l = quant.antecedent
  def quant_r = quant.succedent

  /** Instances of the quantified formulas in the end-sequent. */
  val inst = for (
    ( u, instances ) <- sehs us; if containsQuantifier( u );
    instance <- instances
  ) yield instantiate( u, instance )

  /** Instantiated (previously univ. quantified) formulas on the left. */
  def inst_l = inst.antecedent
  /** Instantiated (previously ex. quantified) formulas on the right. */
  def inst_r = inst.succedent

  // Separating the formulas that contain/don't contain eigenvariables
  private def isVarFree( f: FOLFormula ) = freeVariables( f ) intersect sehs.eigenVariables.flatten.toSet isEmpty
  val varFree = prop ++ inst filter isVarFree
  val alpha = prop ++ inst filterNot isVarFree

  val antecedent = varFree.antecedent
  val antecedent_alpha = alpha.antecedent
  val succedent = varFree.succedent
  val succedent_alpha = alpha.succedent

  val cutImplications = for ( ( ( eigenVar, cutImplInst ), cutFormula ) <- sehs.ss zip cutFormulas )
    yield instantiate( cutFormula, eigenVar ) --> And( cutImplInst map { instantiate( cutFormula, _ ) } )

  def getDeep: HOLSequent = cutImplications ++: ( prop ++ inst )

  override def toString = getDeep.toString
}
