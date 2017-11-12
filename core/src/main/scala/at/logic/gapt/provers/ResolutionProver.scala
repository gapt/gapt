package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution.{ Clausifier, Input, ResolutionProof, ResolutionToExpansionProof, ResolutionToLKProof, mapInputClauses, structuralCNF }
import at.logic.gapt.proofs.{ Context, ContextSection, HOLClause, HOLSequent, MutableContext, Sequent, withSection }
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.lk.{ LKProof, WeakeningContractionMacroRule }
import at.logic.gapt.utils.{ Maybe, NameGenerator }

trait ResolutionProver extends OneShotProver {

  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = getLKProof( seq, addWeakenings = true )

  def getLKProof( seq0: HOLSequent, addWeakenings: Boolean )( implicit ctx0: Maybe[MutableContext] ): Option[LKProof] = {
    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( seq0 ) )
    withSection { section =>
      val seq = section.groundSequent( seq0 )
      getResolutionProof( seq )( ctx ) map { resolution =>
        val lk = ResolutionToLKProof( resolution )
        if ( addWeakenings ) WeakeningContractionMacroRule( lk, seq )
        else lk
      }
    }
  }

  override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
    getResolutionProof( seq )( ctx.map( _.newMutable ) ).isDefined

  def getResolutionProof( cnf: Iterable[ResolutionProof] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] = {
    val cnfMap = cnf.view.map( p => p.conclusion -> p ).toMap
    getResolutionProof( cnfMap.keySet.map( _.map( _.asInstanceOf[Atom] ) ) ) map { resolution =>
      mapInputClauses( resolution )( cnfMap )
    }
  }

  def getResolutionProof( sequentSet: Traversable[HOLSequent] )( implicit ctx0: Maybe[MutableContext], dummyImplicit: DummyImplicit ): Option[ResolutionProof] = {
    implicit val ctx = ctx0.getOrElse( MutableContext.guess( sequentSet ) )
    val cnf = structuralCNF.onProofs(
      sequentSet.map( Input ).toSet,
      propositional = false,
      structural = true,
      bidirectionalDefs = false,
      cse = false )
    getResolutionProof( cnf )( ctx )
  }

  def getResolutionProof( formula: Formula )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] = getResolutionProof( Sequent() :+ formula )
  def getResolutionProof( seq: HOLSequent )( implicit ctx0: Maybe[MutableContext] ): Option[ResolutionProof] = {
    val ctx = ctx0.getOrElse( MutableContext.guess( seq ) )

    val section = new ContextSection( ctx )
    val ground = section.groundSequent( seq )

    val cnf = structuralCNF( ground, propositional = false )( ctx )
    getResolutionProof( cnf )( ctx )
  }

  def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof]

  override def getExpansionProof( seq: HOLSequent )( implicit ctx0: Maybe[MutableContext] ): Option[ExpansionProof] = {
    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( seq ) )
    withSection { section =>
      getResolutionProof( section.groundSequent( seq ) )( ctx ).map( ResolutionToExpansionProof( _ ) )
    }
  }

}
