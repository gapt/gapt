/*
 * rules.scala
 *
 * Proofs are in general acyclic graphs, in order to enforce them being trees just create the right rules as trees and not as acyclic graphs
 */

package at.logic.calculi

import occurrences._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.acyclicGraphs._
import scala.collection.immutable.Set

package proofs {
  
  // exceptions
  class RuleException(msg: String) extends Exception(msg)

  // acyclic graphs like proofs
  abstract class RuleTypeA
  abstract class NullaryRuleTypeA extends RuleTypeA
  abstract class UnaryRuleTypeA extends RuleTypeA
  abstract class BinaryRuleTypeA extends RuleTypeA

  trait Proof[+V] extends AGraph[V] {
    def root = vertex
    def rule: RuleTypeA
    override def toString = rule + "(" + root.toString + ")"
  }
  trait NullaryProof[+V] extends LeafAGraph[V] with Proof[V] {
    override def toString = rule + "(" + root.toString + ")"          
  }
  trait UnaryProof[+V] extends UnaryAGraph[V] with Proof[V] {
    def uProof = t.asInstanceOf[Proof[V]]
    override def toString = rule + "(" + root.toString + ", " + uProof.toString + ")"
  }
  trait BinaryProof[+V] extends BinaryAGraph[V] with Proof[V] {
    def uProof1 = t1.asInstanceOf[Proof[V]]
    def uProof2 = t2.asInstanceOf[Proof[V]]
    override def toString = rule + "(" + root.toString + ", " + uProof1.toString + ", " + uProof2.toString + ")"
  }
}
