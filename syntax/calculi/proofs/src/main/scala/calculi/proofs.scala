/*
 * rules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi

import at.logic.calculi.occurrences._
import at.logic.language.hol.propositions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set

package proofs {
  
  // exceptions
  class RuleException(msg: String) extends Exception(msg)

  // tree like proofs
  abstract class RuleTypeA
  abstract class NullaryRuleTypeA extends RuleTypeA
  abstract class UnaryRuleTypeA extends RuleTypeA
  abstract class BinaryRuleTypeA extends RuleTypeA

  trait Proof[V] extends Tree[V] {
    def root = vertex
    def rule: RuleTypeA
  }
  trait UnaryProof[V] extends UnaryTree[V] with Proof[V] {
    def uProof = t.asInstanceOf[Proof[V]]
  }
  trait BinaryProof[V] extends BinaryTree[V] with Proof[V] {
    def uProof1 = t1.asInstanceOf[Proof[V]]
    def uProof2 = t2.asInstanceOf[Proof[V]]
  }
}
