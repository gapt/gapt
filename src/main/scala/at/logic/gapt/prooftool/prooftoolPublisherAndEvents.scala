package at.logic.gapt.prooftool

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 5, 2010
 * Time: 3:00:53 PM
 */

import at.logic.gapt.proofs.lk.base.Sequent
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.proofs.TreeProof

import scala.swing.event.Event
import scala.swing.{ Color, Publisher }

object ProofToolPublisher extends Publisher
object StructPublisher extends Publisher

case object ProofDbChanged extends Event
case object Loaded extends Event
case object UnLoaded extends Event
case object DisableMenus extends Event
case object EnableMenus extends Event
case object ShowLeaf extends Event
case object HideLeaf extends Event
case object HideTree extends Event
case object HideStructuralRules extends Event
case class ShowAllRules( proof: TreeProof[_] ) extends Event
case class HideProof( proof: TreeProof[_] ) extends Event
case class ShowProof( proof: TreeProof[_] ) extends Event

case class ChangeSequentColor( seqList: Sequent, color: Color, reset: Boolean ) extends Event
case class ChangeFormulaColor( occurrences: Set[FormulaOccurrence], color: Color, reset: Boolean ) extends Event
case class ShowOnly( formulas: Set[FormulaOccurrence], reset: Boolean ) extends Event
