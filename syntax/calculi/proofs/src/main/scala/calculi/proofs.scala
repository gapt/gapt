/*
 * rules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi

import occurrences._
import at.logic.language.hol._
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

  trait Proof[+V] extends Tree[V] {
    def root = vertex
    def rule: RuleTypeA
    override def toString = rule + "(" + root.toString + ")"
  }
  trait UnaryProof[+V] extends UnaryTree[V] with Proof[V] {
    def uProof = t.asInstanceOf[Proof[V]]
    override def toString = rule + "(" + root.toString + ", " + uProof.toString + ")"
  }
  trait BinaryProof[+V] extends BinaryTree[V] with Proof[V] {
    def uProof1 = t1.asInstanceOf[Proof[V]]
    def uProof2 = t2.asInstanceOf[Proof[V]]
    override def toString = rule + "(" + root.toString + ", " + uProof1.toString + ", " + uProof2.toString + ")"
  }
}
