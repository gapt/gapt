package at.logic.gapt.prooftool

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 5, 2010
 * Time: 3:00:53 PM
 */

import at.logic.gapt.proofs.DagProof

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
case class HideEndSequent[T <: DagProof[T]]( proof: DagProof[T] ) extends Event
case class ShowAllRules[T <: DagProof[T]]( proof: DagProof[T] ) extends Event
case class HideProof[T <: DagProof[T]]( proof: DagProof[T] ) extends Event
case class ShowProof[T <: DagProof[T]]( proof: DagProof[T] ) extends Event

