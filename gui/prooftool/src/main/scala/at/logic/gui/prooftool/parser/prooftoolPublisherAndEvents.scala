package at.logic.gui.prooftool.parser

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 5, 2010
 * Time: 3:00:53 PM
 */

import scala.swing.Publisher
import scala.swing.event.Event
import at.logic.calculi.treeProofs.TreeProof

object ProofToolPublisher extends Publisher
object StructPublisher extends Publisher

case object ProofDbChanged extends Event
case object Loaded extends Event
case object UnLoaded extends Event
case object ShowLeaf extends Event
case object HideLeaf extends Event
case object HideTree extends Event
case object HideStructuralRules extends Event
case object ShowAllRules extends Event
case class HideStructural(proof: TreeProof[_]) extends Event