/*
 * agraphProofs.scala
 *
 * Proofs are in general acyclic graphs, in order to enforce them being trees just create the right rules as trees and not as acyclic graphs
 */

package at.logic.calculi.proofs

import at.logic.utils.ds.acyclicGraphs._
import at.logic.utils.ds.trees._

//TODO: after the removal of the toTreeProof method, this is just an alias
trait AGraphProof[V] extends AGraph[V] with Proof[V] {
}
trait NullaryAGraphProof[V] extends LeafAGraph[V] with NullaryProof[V] with AGraphProof[V] {
}
trait UnaryAGraphProof[V] extends UnaryAGraph[V] with UnaryProof[V] with AGraphProof[V] {
}
trait BinaryAGraphProof[V] extends BinaryAGraph[V] with BinaryProof[V] with AGraphProof[V] {
}
