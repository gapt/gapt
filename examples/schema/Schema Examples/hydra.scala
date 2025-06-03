


import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.Sequent
import gapt.proofs.ceres.CharacteristicClauseSet
import gapt.proofs.ceres.StructCreators
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.util.instantiateProof
import gapt.proofs.lk.transformations.cutNormal

import gapt.proofs.lk.util.isCutFree
import gapt.proofs.expansion.numberOfInstancesET

import gapt.expr.schema.Numeral


/**
  * Two-Hydra Example from:
      Berardi, S. (2019). 
      EXPLICIT INDUCTION IS NOT EQUIVALENT TO CYCLIC PROOFS FOR CLASSICAL LOGIC WITH INDUCTIVE DEFINITIONS. 
      LOGICAL METHODS IN COMPUTER SCIENCE, 15(3), 1-25.
 
  */



object hydra extends TacticsProof {

def simulateHydra(h1: Int, h2: Int, steps: Int): List[(Int, Int)] = {
  require(h1 >= 0 && h2 >= 0 && steps >= 0, "Heads and steps must be non-negative")

  def isWinningState(x: Int, y: Int): Boolean =
    (x, y) match {
      case (0, 0) => true
      case (1, 0) => true
      case (_, 1) => true
      case _      => false
    }

  def nextState(n: Int, m: Int): Option[((Int, Int), Int)] = {
    if (n >= 1 && m >= 2) Some(((n - 1, m - 2), 2))
    else if (n == 0 && m >= 2) Some(((m - 1, m - 2), 3))
    else if (m == 0 && n >= 2) Some(((n - 1, n - 2), 4))
    else None
  }

  def loop(n: Int, m: Int, remaining: Int, acc: List[(Int, Int)]): List[(Int, Int)] = {
    if (isWinningState(n, m)) {
      println(s"Winning state reached: ($n, $m)")
      acc :+ (n, m)
    } else if (remaining == 0) {
      println(s"Steps exhausted. Hydra not yet defeated. Last state: ($n, $m)")
      acc :+ (n, m)
    } else {
      nextState(n, m) match {
        case Some(((n1, m1), rule)) =>
          println(s"($n, $m) ⟶ ($n1, $m1)   via rule $rule")
          loop(n1, m1, remaining - 1, acc :+ (n, m))
        case None =>
          println(s"Error: No further transitions. Stuck at state: ($n, $m)")
          acc :+ (n, m)
      }
    }
  }

  val result = loop(h1, h2, steps, List())
  result
}

}