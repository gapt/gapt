
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


import java.io.{File, PrintWriter}


/**
  * Two-Hydra Example from:
      Berardi, S. (2019). 
      EXPLICIT INDUCTION IS NOT EQUIVALENT TO CYCLIC PROOFS FOR CLASSICAL LOGIC WITH INDUCTIVE DEFINITIONS. 
      LOGICAL METHODS IN COMPUTER SCIENCE, 15(3), 1-25.

  */

  /* 
    Implemented using the adjusted rule definitions. (Using the predecessor instead of the successor)

    - ( H_a ) \forall u :   P(0,0) \land P(1,0) \land P(u,1)
    - ( H_b ) \forall u,v : P(pu,ppv) \to P(u,v)
    - ( H_c ) \forall v :   P(pv,ppv) \to P(0,v)
    - ( H_d ) \forall u :   P(pu,ppu) \to P(u, 0)

   */


object hydraSubstitutionsPred extends TacticsProof {

  /** Simulates the hydra and returns both states and substitutions. */
  def simulateHydra(h1: Int, h2: Int, steps: Int): (List[(Int, Int)], List[Map[String, String]]) = {
    require(h1 >= 0 && h2 >= 0 && steps >= 0, "Heads and steps must be non-negative")

    def isWinningState(x: Int, y: Int): Boolean =
      (x, y) match {
        case (0, 0) => true
        case (1, 0) => true
        case (_, 1) => true
        case _      => false
      }

    /** Computes next state and its substitution, numbering X and Y separately */
    def nextStateWithSubstitution(
        n: Int,
        m: Int,
        xIndex: Int,
        yIndex: Int
    ): Option[((Int, Int), String, Map[String, String], Int, Int)] = {

      if (n >= 1 && m >= 2) {
        // Rule B2: (n, m) -> (n-1, m-2)
        val next = (n - 1, m - 2)
        val subs = Map(s"X($xIndex)" -> n.toString, s"Y($yIndex)" -> m.toString)
        Some((next, "B2", subs, xIndex + 1, yIndex + 1))

      } else if (n == 0 && m >= 2) {
        // Rule C3: (0, m) -> (m-1, m-2)
        val next = (m - 1, m - 2)
        val subs = Map(s"Y($yIndex)" -> m.toString)
        Some((next, "C3", subs, xIndex, yIndex + 1))

      } else if (m == 0 && n >= 2) {
        // Rule D4: (n, 0) -> (n-1, n-2)
        val next = (n - 1, n - 2)
        val subs = Map(s"X($xIndex)" -> n.toString)
        Some((next, "D4", subs, xIndex + 1, yIndex))

      } else None
    }

    /** Main recursive loop */
    def loop(
        n: Int,
        m: Int,
        remaining: Int,
        acc: List[(Int, Int)],
        subsAcc: List[Map[String, String]],
        xCounter: Int,
        yCounter: Int
    ): (List[(Int, Int)], List[Map[String, String]]) = {

      if (isWinningState(n, m)) {
        // Add special substitution for (_, 1)
        val extraSub: Option[Map[String, String]] =
          if (m == 1) Some(Map(s"X($xCounter)" -> n.toString))
          else None

        val newSubsAcc = extraSub match {
          case Some(sub) =>
            println(s"Winning state reached: ($n, $m) — extra substitution {X($xCounter) <- $n}")
            subsAcc :+ sub
          case None =>
            println(s"Winning state reached: ($n, $m)")
            subsAcc
        }

        (acc :+ (n, m), newSubsAcc)

      } else if (remaining == 0) {
        println(s"Steps exhausted. Hydra not yet defeated. Last state: ($n, $m)")
        (acc :+ (n, m), subsAcc)

      } else {
        nextStateWithSubstitution(n, m, xCounter, yCounter) match {
          case Some(((n1, m1), rule, subs, nextX, nextY)) =>
            val subsStr = subs.map { case (k, v) => s"$k <- $v" }.mkString(", ")
            println(f"($n, $m) ⟶ ($n1, $m1)   via rule $rule with substitution {$subsStr}")
            loop(n1, m1, remaining - 1, acc :+ (n, m), subsAcc :+ subs, nextX, nextY)

          case None =>
            println(s"Error: No further transitions. Stuck at state: ($n, $m)")
            (acc :+ (n, m), subsAcc)
        }
      }
    }

    val (resultStates, substitutions) = loop(h1, h2, steps, List(), List(), 1, 1)
    println(s"\n val res: List[(Int, Int)] = $resultStates \n")
    println(prettyPrintSubstitutions(substitutions))
    (resultStates, substitutions)
  }

  /** Pretty-prints the list of substitutions */
  def prettyPrintSubstitutions(subsList: List[Map[String, String]]): String = {
    if (subsList.isEmpty) "No substitutions."
    else {
      val formatted = subsList.zipWithIndex.map { case (subs, i) =>
        val body = subs.map { case (k, v) => s"$k <- $v" }.mkString(", ")
        s"Step ${i + 1}: { $body }"
      }
      "Substitution history:\n" + formatted.mkString("\n")  + "\n"
    }
  }

  /** Runs hydra simulations for all (h1,h2) pairs in given ranges and saves only substitution histories to a text file. */
  def exportSubstitutionHistoriesTxtRange(
      h1Range: Range,
      h2Range: Range,
      steps: Int,
      outputPath: String = "hydra_substitutions_range.txt"
  ): Unit = {

    val file = new File(outputPath)
    val writer = new PrintWriter(file)

    val runs = for {
      h1 <- h1Range
      h2 <- h2Range
    } yield (h1, h2)

    runs.zipWithIndex.foreach { case ((h1, h2), i) =>
      val (_, substitutions) = simulateHydra(h1, h2, steps)

      writer.println(s"Hydra Simulation #${i + 1}")
      writer.println(s"Start State: ($h1, $h2)")
      writer.println("-" * 40)
      writer.println(prettyPrintSubstitutions(substitutions))
      writer.println("\n")
    }

    writer.close()
    println(s"Text file created successfully at: ${file.getAbsolutePath}")
  }

}
