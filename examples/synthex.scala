import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{HOLSequent, Sequent}
import at.logic.gapt.proofs.expansion.{Deskolemize, Pr, eigenVariablesET}
import at.logic.gapt.proofs.lk.{LKProof, skolemize}
import at.logic.gapt.prooftool.DrawSequent
//import at.logic.gapt.proofs.resolution.{RobinsonToExpansionProof, RobinsonToLK}
import at.logic.gapt.provers.vampire.Vampire
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, ExpansionTree }
import at.logic.gapt.proofs.lk.{ LKToExpansionProof, consoleString }

import collection.immutable.Map

object synthex extends Script {

  val peano5 = hof"!x 0 = x*0"
  val peano7 = hof"!x!y (x<y -> s(x)<s(y))"
  val lem1 = hof"!x s(pow2(s x)) < pow2(s(s x))"
  val lem2 = hof"!x pow2(x) < pow2(s x)"
  val lem4 = hof"!x!y (y<x | x<y | x=y)"
  val lem5 = hof"!x!y!z (y<z & x<y -> x<z)"
  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val defpow2 = hof"!x x*x = pow2(x)"
  val defind = hof"!x (i(x) <-> ?y (x < pow2(s y) & pow2(y) <= x))"
  val thm1 = hof"""!y!x (
    s(x)<pow2(s y) & x<pow2(s y) & pow2(y)<=x ->
      s(x)<pow2(s y) & pow2(y)<=s(x)
  )"""
  val ind = hof"!x (i x -> i(s x)) & i 0 -> !x i x"

  val thm = hof"!x i(x)"

  //val problem = peano5 +: peano7 +: lem1 +: lem2 +: lem4 +: lem5 +:
  //  defleq +: defpow2 +: defind +: ind +: thm1 +: Sequent() :+ thm

  val problem = Sequent() :+ hof"?x (P x -> !y (x = x & P y))"
  println( "Problem" )
  println( problem )

  val expansionProof: Option[ExpansionProof] = Vampire getExpansionProof problem

  val expansionSequent: Sequent[ExpansionTree] = expansionProof.get.expansionSequent

  println( "ExpansionSequent" )
  println( expansionSequent )


  println( variables(expansionSequent.shallow) )
  val desk: Sequent[ExpansionTree] = Deskolemize(expansionSequent)
  println(desk)

  println(ExpansionProofToLK(ExpansionProof(desk)))
}
