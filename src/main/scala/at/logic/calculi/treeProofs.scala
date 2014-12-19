/*
 * treeProofs.scala
 *
 * Proofs are in general acyclic graphs, in order to enforce them being trees just create the right rules as trees and not as acyclic graphs
 */

package at.logic.calculi.proofs

import at.logic.utils.ds.trees._

trait TreeProof[V] extends Tree[V] with Proof[V]
trait NullaryTreeProof[V] extends LeafTree[V] with NullaryProof[V] with TreeProof[V]
trait UnaryTreeProof[V] extends UnaryTree[V] with UnaryProof[V] with TreeProof[V]
trait BinaryTreeProof[V] extends BinaryTree[V] with BinaryProof[V] with TreeProof[V] 
