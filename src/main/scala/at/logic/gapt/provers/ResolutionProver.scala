package at.logic.gapt.provers

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr.Const
import at.logic.gapt.expr.hol.structuralCNF
import at.logic.gapt.proofs.resolution.{ ResolutionProof, RobinsonToLK, RobinsonToExpansionProof }
import at.logic.gapt.proofs.{ HOLClause, HOLSequent }
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import at.logic.gapt.proofs.lkNew.LKProof

abstract class ResolutionProver extends OneShotProver {

  protected def withRenamedConstants( cnf: Traversable[HOLClause] )( f: ( Map[Const, Const], List[HOLClause] ) => Option[ResolutionProof] ): Option[ResolutionProof] = {
    val ( renamedCNF, renaming, invertRenaming ) = renameConstantsToFi( cnf.toList )
    f( renaming, renamedCNF ) map { renamedProof =>
      TermReplacement( renamedProof, invertRenaming toMap )
    }
  }

  private def withGroundVariables( seq: HOLSequent )( f: HOLSequent => Option[LKProof] ): Option[LKProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      TermReplacement( renamedProof, invertRenaming toMap )
    }
  }

  private def withGroundVariables2( seq: HOLSequent )( f: HOLSequent => Option[ExpansionSequent] ): Option[ExpansionSequent] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      renamedProof map { TermReplacement( _, invertRenaming ) }
    }
  }

  private def withGroundVariables3( seq: HOLSequent )( f: HOLSequent => Option[ResolutionProof] ): Option[ResolutionProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      TermReplacement( renamedProof, invertRenaming )
    }
  }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    withGroundVariables( seq ) { seq =>
      val ( cnf, justs, defs ) = structuralCNF( seq, generateJustifications = true, propositional = false )
      getRobinsonProof( seq ) map { robinsonProof =>
        RobinsonToLK( robinsonProof, seq, justs toMap, defs )
      }
    }

  override def isValid( seq: HOLSequent ): Boolean =
    getRobinsonProof( seq ).isDefined

  def getRobinsonProof( seq: HOLSequent ): Option[ResolutionProof] =
    withGroundVariables3( seq ) { seq =>
      getRobinsonProof( structuralCNF( seq, generateJustifications = false, propositional = false )._1 )
    }

  def getRobinsonProof( seq: Traversable[HOLClause] ): Option[ResolutionProof]

  override def getExpansionSequent( seq: HOLSequent ): Option[ExpansionSequent] =
    withGroundVariables2( seq ) { seq =>
      val ( cnf, justs, defs ) = structuralCNF( seq, generateJustifications = true, propositional = false )
      getRobinsonProof( cnf ).map( RobinsonToExpansionProof( _, seq, justs, defs ) )
    }

}
