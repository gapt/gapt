package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.ceres.{ CharacteristicClauseSet, extractStruct }
import at.logic.gapt.proofs.lk.AtomicExpansion
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.provers.spass.SPASS

object ReductionDemo extends Script {
  //  val sequent = groundFreeVariables( nTape3.expansion_proof.deep )._1
  //  val sequent = CharacteristicClauseSet( extractStruct( AtomicExpansion( prime.prime( 3 ).proof ) ) ).map { cls => univclosure( cls.toImplication ) } ++: Sequent()
  val sequent = hof"∀f P(f) = f(c)" +: Sequent() :+ hof"P(λx h(h(x))) = h(h(c))"
  //  val sequent = groundFreeVariables( eliminateCutsET( LKToExpansionProof( nTape3.preprocessed_input_proof ) ).deep )._1

  val reduction =
    LambdaEliminationReduction |>
      HOFunctionReduction |>
      PredicateReductionET |>
      ErasureReductionET

  val ( redSeq, _ ) = reduction forward sequent
  println( TPTPFOLExporter.tptp_proof_problem_split( redSeq ) )
  println( redSeq )
  println( SPASS getExpansionProof redSeq )

}