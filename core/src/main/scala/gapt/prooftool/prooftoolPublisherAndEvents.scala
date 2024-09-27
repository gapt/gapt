package gapt.prooftool

import java.awt.Color

import gapt.proofs.{DagProof, SequentIndex, SequentProof}

import scala.swing.event.Event
import scala.swing.{Color, Component, Publisher, Reactor}

class ProofToolPublisher extends Publisher

case object ShowLeaf extends Event
case object HideLeaf extends Event
case object HideTree extends Event
case object HideStructuralRules extends Event
case class HideEndSequent(pos: List[Int]) extends Event
case class ShowAllRules(pos: List[Int]) extends Event
case class HideProof(pos: List[Int]) extends Event
case class ShowProof(pos: List[Int]) extends Event
case class HideSequentProof(pos: List[Int]) extends Event
case class ShowSequentProof(pos: List[Int]) extends Event
case object HideSequentContexts extends Event
case object ShowAllFormulas extends Event
case object MarkCutAncestors extends Event
case object UnmarkCutAncestors extends Event
case class MarkOccurrences(p: List[Int], is: Set[SequentIndex]) extends Event
case object UnmarkAllFormulas extends Event
case object FontChanged extends Event
case object AlignmentChanged extends Event

case object ShowDebugBorders extends Event
case object HideDebugBorders extends Event
