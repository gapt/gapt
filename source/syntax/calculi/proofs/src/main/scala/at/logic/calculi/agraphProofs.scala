/*
 * agraphProofs.scala
 *
 * Proofs are in general acyclic graphs, in order to enforce them being trees just create the right rules as trees and not as acyclic graphs
 */

package at.logic.calculi.proofs

import at.logic.utils.ds.acyclicGraphs._
import at.logic.utils.ds.trees._

trait AGraphProof[V] extends AGraph[V] with Proof[V] {
    def toTreeProof: TreeProof[V]
}
trait NullaryAGraphProof[V] extends LeafAGraph[V] with NullaryProof[V] with AGraphProof[V] {
  def toTreeProof = new LeafTree[V](vertex) with NullaryProof[V] with TreeProof[V] { def rule = this.rule}
}
trait UnaryAGraphProof[V] extends UnaryAGraph[V] with UnaryProof[V] with AGraphProof[V] {
  def toTreeProof = new UnaryTree[V](vertex, t.asInstanceOf[AGraphProof[V]].toTreeProof) with UnaryProof[V] with TreeProof[V] { def rule = this.rule}
}
trait BinaryAGraphProof[V] extends BinaryAGraph[V] with BinaryProof[V] with AGraphProof[V] {
  def toTreeProof = new BinaryTree[V](vertex, t1.asInstanceOf[AGraphProof[V]].toTreeProof, t2.asInstanceOf[AGraphProof[V]].toTreeProof) with BinaryProof[V] with TreeProof[V] { def rule = this.rule}
}
