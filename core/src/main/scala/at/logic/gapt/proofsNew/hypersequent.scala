package at.logic.gapt.proofsNew

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofsNew.lk.LKInference

class HypersequentCalculus[BaseJdg, BaseInf <: Inference[BaseJdg]] {
  type Jdg = Vector[BaseJdg]

  trait Inf extends Inference[Jdg]

  type Proof = DagProof[Jdg, Inf]

  case class ExternalWeakening( premise: Jdg, sequent: BaseJdg ) extends Inf {
    val premises = Vector( premise )
    val conclusion = premise :+ sequent
  }

  case class ExternalContraction( premise: Jdg, i: Int, j: Int ) extends Inf {
    require( premise( i ) == premise( j ) )
    val premises = Vector( premise )
    val conclusion = ( premise.view.zipWithIndex.filter( k => k._2 != i && k._2 != j ).map( _._1 ) :+ premise( i ) ).toVector
  }

  case class InternalInference( premises: Vector[Jdg], is: Vector[Int], inf: BaseInf ) extends Inf {
    require( premises.size == is.size )
    require( inf.premises == ( premises, is ).zipped.map( _( _ ) ) )
    val internalConclusion = inf.conclusion
    val conclusion: Jdg =
      ( premises, is ).zipped.flatMap( ( p, i ) =>
        p.view.zipWithIndex.filterNot( _._2 == i ).map( _._1 ) ) :+ internalConclusion
  }
}

object HypersequentLK extends HypersequentCalculus[HOLSequent, LKInference]
