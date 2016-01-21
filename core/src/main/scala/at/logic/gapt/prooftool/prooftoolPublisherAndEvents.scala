package at.logic.gapt.prooftool

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 5, 2010
 * Time: 3:00:53 PM
 */

import at.logic.gapt.proofs.DagProof
import at.logic.gapt.proofs.lkOld.base.OccSequent
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.proofs.TreeProof

import scala.swing.event.Event
import scala.swing.{ Color, Publisher }

class ProofToolPublisher extends Publisher

case object ProofDbChanged extends Event
case object DisableMenus extends Event
case object EnableMenus extends Event
case object ShowLeaf extends Event
case object HideLeaf extends Event
case object HideTree extends Event
case object HideStructuralRules extends Event
case class ShowAllRules[T <: DagProof[T]]( proof: DagProof[T] ) extends Event
case class ShowAllRulesOld[T]( proof: TreeProof[T] ) extends Event
case class HideProof[T <: DagProof[T]]( proof: DagProof[T] ) extends Event
case class ShowProof[T <: DagProof[T]]( proof: DagProof[T] ) extends Event

case class ChangeSequentColor( seqList: OccSequent, color: Color, reset: Boolean ) extends Event
case class ChangeFormulaColor( occurrences: Set[FormulaOccurrence], color: Color, reset: Boolean ) extends Event
case class ShowOnly( formulas: Set[FormulaOccurrence], reset: Boolean ) extends Event
