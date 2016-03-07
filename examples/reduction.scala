package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.atoms
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.{ Context, FiniteContext }
import at.logic.gapt.provers.spass.SPASS

object ReductionDemo extends Script {
  val deep = nTape3.expansion_proof.deep
  //  val deep = hof"∀f P(f) = f(c)" +: Sequent() :+ hof"P(λx h(h(x))) = h(h(c))"

  implicit var ctx = FiniteContext()
  ctx += Context.Sort( "i" )
  ctx ++= constants( deep )

  val lambdas = atoms( deep ).flatMap { subTerms( _ ) }.collect { case a: Abs => a }.toSet
  val hoTypes = variables( deep ).map { _.exptype }.filter { !_.isInstanceOf[TBase] }
  val reduction =
    LambdaEliminationReduction( ctx, lambdas ) |>
      HOFunctionReduction |>
      PredicateReduction |> ErasureReduction
  //  println(TPTPFOLExporter.tptp_proof_problem_split(reduction.forward(deep)))
  println( reduction forward deep )
  println( SPASS getRobinsonProof reduction.forward( deep ) )

}