package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.atoms
import at.logic.gapt.proofs.expansion.{ ExpansionProof, eliminateCutsET }
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.{ Context, FiniteContext, HOLSequent, Sequent }
import at.logic.gapt.provers.groundFreeVariables
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.spass.SPASS

object ReductionDemo extends Script {
  val sequent = groundFreeVariables( nTape3.expansion_proof.deep )._1
  //  val sequent = hof"∀f P(f) = f(c)" +: Sequent() :+ hof"P(λx h(h(x))) = h(h(c))"
  //  val sequent = groundFreeVariables( eliminateCutsET( LKToExpansionProof( nTape3.preprocessed_input_proof ) ).deep )._1

  implicit var ctx = FiniteContext()
  ctx += Context.Sort( "i" )
  ctx ++= constants( sequent )

  val lambdas = atoms( sequent ).flatMap { subTerms( _ ) }.collect { case a: Abs => a }.toSet
  val reduction =
    LambdaEliminationReduction |>
      HOFunctionReduction |>
      PredicateReductionET |> ErasureReductionET
  //  println(TPTPFOLExporter.tptp_proof_problem_split(reduction.forward(deep)))
  println( reduction forward sequent _1 )
  println( SPASS getRobinsonProof reduction.forward( sequent )._1 )

}