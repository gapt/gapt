package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.ceres.{ CharacteristicClauseSet, extractStruct }
import at.logic.gapt.proofs.lk.{ AtomicExpansion, LKToExpansionProof }
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.eliminateCutsET
import at.logic.gapt.proofs.resolution.{ Input, eliminateSplitting, simplifyResolutionProof }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.groundFreeVariables
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.vampire.Vampire

object ReductionDemo extends Script {
  //  val sequent = groundFreeVariables( nTape3.expansion_proof.deep )._1
  //  val sequent = CharacteristicClauseSet( extractStruct( AtomicExpansion( prime.prime( 3 ).proof ) ) ).map { cls => univclosure( cls.toImplication ) } ++: Sequent()
  val sequent = hof"∀f P(f) = f(c)" +: Sequent() :+ hof"P(λx h(h(x))) = h(h(c))"
  //  val sequent = groundFreeVariables( eliminateCutsET( LKToExpansionProof( nTape3.preprocessed_input_proof ) ).deep )._1

  val reduction =
    LambdaEliminationReductionRes |>
      HOFunctionReductionRes |>
      CNFReductionResRes |>
      PredicateReductionCNF |>
      ErasureReductionCNF

  val ( redSeq, back ) = reduction forward sequent
  println( TPTPFOLExporter( redSeq ) )
  println()
  var Some( res ) = Vampire getResolutionProof redSeq
  var res_ = back( simplifyResolutionProof( eliminateSplitting( res ) ) )
  println( s"Found a proof with ${res_.dagLike.size} inferences:" )
  println( res_ )

  for ( Input( seq ) <- res_.subProofs )
    require( sequent.contains( seq.elements.head, seq.antecedent.nonEmpty ) )

}