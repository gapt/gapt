package gapt.provers

import gapt.expr._
import gapt.proofs.resolution.{ Clausifier, Input, ResolutionProof, ResolutionToExpansionProof, ResolutionToLKProof, eliminateSplitting, mapInputClauses, structuralCNF }
import gapt.proofs.{ Context, ContextSection, HOLClause, HOLSequent, MutableContext, Sequent, withSection }
import gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, deskolemizeET }
import gapt.proofs.lk.{ LKProof, LKToExpansionProof, WeakeningContractionMacroRule }
import gapt.utils.{ Maybe, NameGenerator }

trait ResolutionProver extends OneShotProver { self =>

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

  def extendToManySortedViaPredicates = new ResolutionProver {
    import gapt.proofs.reduction._
    override def isValid( sequent: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = {
      val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
      val ( folProblem, _ ) = reduction forward sequent
      self.getResolutionProof( folProblem )( ctx.map( _.newMutable ) ).isDefined
    }

    override def getExpansionProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
      val reduction = PredicateReductionET |> ErasureReductionET
      val ( folProblem, back ) = reduction forward sequent
      self.getExpansionProof( folProblem ).map( back )
    }

    override def getLKProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = {
      val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
      val ( folProblem, back ) = reduction forward sequent
      self.getResolutionProof( folProblem ).map( proof => back( eliminateSplitting( proof ) ) )
    }

    override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] = {
      val reduction = PredicateReductionCNF |> ErasureReductionCNF
      val ( folProblem, back ) = reduction forward seq.toSet
      self.getResolutionProof( folProblem ).map( back )
    }

    override def toString = s"$self.extendToManySortedViaPredicates"
  }

  def extendToManySortedViaErasure = new ResolutionProver {
    import gapt.proofs.reduction._
    override def isValid( sequent: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = {
      val reduction = CNFReductionLKRes |> ErasureReductionCNF
      val ( folProblem, _ ) = reduction forward sequent
      self.getResolutionProof( folProblem )( ctx.map( _.newMutable ) ).isDefined
    }

    override def getExpansionProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
      val reduction = ErasureReductionET
      val ( folProblem, back ) = reduction forward sequent
      self.getExpansionProof( folProblem ).map( back )
    }

    override def getLKProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = {
      val reduction = CNFReductionLKRes |> ErasureReductionCNF
      val ( folProblem, back ) = reduction forward sequent
      self.getResolutionProof( folProblem ).map( proof => back( eliminateSplitting( proof ) ) )
    }

    override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] = {
      val reduction = ErasureReductionCNF
      val ( folProblem, back ) = reduction forward seq.toSet
      self.getResolutionProof( folProblem ).map( back )
    }

    override def toString = s"$self.extendToManySortedViaErasure"
  }

  def withDeskolemization = new ResolutionProver {
    override def isValid( sequent: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
      self.isValid( sequent )

    override def getExpansionProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] =
      self.getExpansionProof( sequent ).map( deskolemizeET( _ ) )

    override def getLKProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
      getExpansionProof( sequent ).flatMap( ep => ExpansionProofToLK( ep ) match {
        case Right( lk ) => Some( lk )
        case Left( _ )   => None
      } )

    override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
      self.getResolutionProof( seq )

    override def toString = s"$self.withDeskolemization"
  }

}
