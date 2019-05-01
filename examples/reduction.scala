package gapt.examples

import gapt.expr._
import gapt.expr.formula.hol.universalClosure
import gapt.formats.tptp.TptpFOLExporter
import gapt.proofs.ceres.{ CharacteristicClauseSet, extractStruct }
import gapt.proofs.reduction._
import gapt.proofs.Sequent
import gapt.proofs.expansion.eliminateCutsET
import gapt.proofs.lk.util.AtomicExpansion
import gapt.proofs.resolution.{ Input, eliminateSplitting, simplifyResolutionProof }
import gapt.provers.escargot.Escargot
import gapt.provers.groundFreeVariables
import gapt.provers.spass.SPASS
import gapt.provers.vampire.Vampire

object ReductionDemo extends Script {
  //  val sequent = groundFreeVariables( nTape3.expansion_proof.deep )._1
  //  val sequent = CharacteristicClauseSet( extractStruct( AtomicExpansion( prime.prime( 3 ).proof ) ) ).map { cls => univclosure( cls.toImplication ) } ++: Sequent()
  val sequent = hof"∀f P(f) = f(c)" +: Sequent() :+ hof"P(λx h(h(x))) = h(h(c))"
  //  val sequent = groundFreeVariables( eliminateCutsET( LKToExpansionProof( nTape3.preprocessed_input_proof ) ).deep )._1

  val reduction =
    LambdaEliminationReductionRes() |>
      HOFunctionReductionRes() |>
      CNFReductionResRes |>
      PredicateReductionCNF |>
      ErasureReductionCNF

  val ( redSeq, back ) = reduction forward sequent
  println( TptpFOLExporter( redSeq ) )
  println()
  var Some( res ) = Vampire getResolutionProof redSeq
  var res_ = back( simplifyResolutionProof( eliminateSplitting( res ) ) )
  println( s"Found a proof with ${res_.dagLike.size} inferences:" )
  println( res_ )

  for ( Input( seq ) <- res_.subProofs )
    require( sequent.contains( seq.elements.head, !seq.indices.head.polarity ) )

}