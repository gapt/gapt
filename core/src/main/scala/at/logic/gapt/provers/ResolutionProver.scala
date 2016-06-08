package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, ResolutionToExpansionProof, ResolutionToLKProof, mapInputClauses, structuralCNF }
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.lk.{ LKProof, WeakeningContractionMacroRule }

trait ResolutionProver extends OneShotProver {

  protected def withRenamedConstants( cnf: Traversable[HOLClause] )( f: ( Map[Const, Const], Traversable[HOLClause] ) => Option[ResolutionProof] ): Option[ResolutionProof] = {
    val ( renamedCNF, renaming, invertRenaming ) = renameConstantsToFi( cnf.toList )
    f( renaming, renamedCNF ) map { renamedProof =>
      TermReplacement( renamedProof, invertRenaming toMap )
    }
  }

  private def withGroundVariables( seq: HOLSequent )( f: HOLSequent => Option[LKProof] ): Option[LKProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      val usedVars = renamedProof.subProofs.flatMap { p => variables( p ) }
      val varRenaming = rename( invertRenaming.values, usedVars )
      Substitution( varRenaming.map( _.swap ) )( TermReplacement( renamedProof, invertRenaming.mapValues( varRenaming ).toMap[LambdaExpression, LambdaExpression] ) )
    }
  }

  private def withGroundVariables2( seq: HOLSequent )( f: HOLSequent => Option[ExpansionProof] ): Option[ExpansionProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map {
      case ExpansionProof( renamedExpSeq ) =>
        ExpansionProof( renamedExpSeq map { TermReplacement( _, invertRenaming.toMap ) } )
    }
  }

  private def withGroundVariables3( seq: HOLSequent )( f: HOLSequent => Option[ResolutionProof] ): Option[ResolutionProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      TermReplacement( renamedProof, invertRenaming.toMap )
    }
  }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] = getLKProof( seq, addWeakenings = true )

  def getLKProof( seq: HOLSequent, addWeakenings: Boolean ): Option[LKProof] =
    withGroundVariables( seq ) { seq =>
      getResolutionProof( seq ) map { resolution =>
        val lk = ResolutionToLKProof( resolution )
        if ( addWeakenings ) WeakeningContractionMacroRule( lk, seq )
        else lk
      }
    }

  override def isValid( seq: HOLSequent ): Boolean =
    getResolutionProof( seq ).isDefined

  @deprecated( "Use getResolutionProof instead.", "2.2" )
  def getRobinsonProof( cnf: Iterable[ResolutionProof] ): Option[ResolutionProof] = getResolutionProof( cnf )
  @deprecated( "Use getResolutionProof instead.", "2.2" )
  def getRobinsonProof( formula: HOLFormula ): Option[ResolutionProof] = getResolutionProof( formula )
  @deprecated( "Use getResolutionProof instead.", "2.2" )
  def getRobinsonProof( seq: HOLSequent ): Option[ResolutionProof] = getResolutionProof( seq )
  @deprecated( "Use getResolutionProof instead.", "2.2" )
  def getRobinsonProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] = getResolutionProof( seq )

  def getResolutionProof( cnf: Iterable[ResolutionProof] ): Option[ResolutionProof] = {
    val cnfMap = cnf.view.map( p => p.conclusion -> p ).toMap
    getResolutionProof( cnfMap.keySet.map( _.map( _.asInstanceOf[HOLAtom] ) ) ) map { resolution =>
      mapInputClauses( resolution, factorEarly = true )( cnfMap )
    }
  }

  def getResolutionProof( formula: HOLFormula ): Option[ResolutionProof] = getResolutionProof( Sequent() :+ formula )
  def getResolutionProof( seq: HOLSequent ): Option[ResolutionProof] = {
    val cnf = structuralCNF( groundFreeVariables( seq )._1, propositional = false )
    getResolutionProof( cnf )
  }

  def getResolutionProof( seq: Traversable[HOLClause] ): Option[ResolutionProof]

  override def getExpansionProof( seq: HOLSequent ): Option[ExpansionProof] =
    withGroundVariables2( seq ) { seq =>
      getResolutionProof( seq ) map { ResolutionToExpansionProof( _ ) }
    }

}
