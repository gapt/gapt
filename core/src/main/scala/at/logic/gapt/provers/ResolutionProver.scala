package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution.{ Clausifier, Input, ResolutionProof, ResolutionToExpansionProof, ResolutionToLKProof, mapInputClauses, structuralCNF }
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.lk.{ LKProof, WeakeningContractionMacroRule }

trait ResolutionProver extends OneShotProver {

  override def getLKProof( seq: HOLSequent ): Option[LKProof] = getLKProof( seq, addWeakenings = true )

  def getLKProof( seq: HOLSequent, addWeakenings: Boolean ): Option[LKProof] =
    groundFreeVariables.wrap( seq ) { seq =>
      getResolutionProof( seq ) map { resolution =>
        val lk = ResolutionToLKProof( resolution )
        if ( addWeakenings ) WeakeningContractionMacroRule( lk, seq )
        else lk
      }
    }

  override def isValid( seq: HOLSequent ): Boolean =
    getResolutionProof( seq ).isDefined

  def getResolutionProof( cnf: Iterable[ResolutionProof] ): Option[ResolutionProof] = {
    val cnfMap = cnf.view.map( p => p.conclusion -> p ).toMap
    getResolutionProof( cnfMap.keySet.map( _.map( _.asInstanceOf[HOLAtom] ) ) ) map { resolution =>
      mapInputClauses( resolution )( cnfMap )
    }
  }

  def getResolutionProof( sequentSet: Traversable[HOLSequent] )( implicit dummyImplicit: DummyImplicit ): Option[ResolutionProof] = {
    val clausifier = new Clausifier(
      propositional = false, structural = true, bidirectionalDefs = false,
      nameGen = rename.awayFrom( sequentSet.view.flatMap( constants( _ ) ).toSet )
    )
    for ( sequent <- sequentSet ) clausifier.expand( Input( sequent ) )
    getResolutionProof( clausifier.cnf )
  }

  def getResolutionProof( formula: HOLFormula ): Option[ResolutionProof] = getResolutionProof( Sequent() :+ formula )
  def getResolutionProof( seq: HOLSequent ): Option[ResolutionProof] = {
    val cnf = structuralCNF( groundFreeVariables( seq )._1, propositional = false )
    getResolutionProof( cnf )
  }

  def getResolutionProof( seq: Traversable[HOLClause] ): Option[ResolutionProof]

  override def getExpansionProof( seq: HOLSequent ): Option[ExpansionProof] =
    groundFreeVariables.wrap( seq ) { seq =>
      getResolutionProof( seq ) map { ResolutionToExpansionProof( _ ) }
    }

}
