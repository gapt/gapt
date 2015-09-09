package at.logic.gapt.provers

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.expr.{ FOLConst, Const }
import at.logic.gapt.expr.hol.CNFn
import at.logic.gapt.proofs.resolution.{ RobinsonToLK, RobinsonToExpansionProof }
import at.logic.gapt.proofs.{ HOLClause, HOLSequent }
import at.logic.gapt.proofs.expansionTrees.{ replace, InstanceTermEncoding, ExpansionSequent }
import at.logic.gapt.proofs.lk.applyReplacement
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.proofs.resolutionOld.robinson.RobinsonResolutionProof

abstract class ResolutionProver extends Prover {

  protected def withRenamedConstants( cnf: Traversable[HOLClause] )( f: ( Map[Const, String], List[HOLClause] ) => Option[RobinsonResolutionProof] ): Option[RobinsonResolutionProof] = {
    val ( renamedCNF, renaming, invertRenaming ) = renameConstantsToFi( cnf.toList )
    f( renaming, renamedCNF ) map { renamedProof =>
      NameReplacement( renamedProof, invertRenaming )
    }
  }

  private def withGroundVariables( seq: HOLSequent )( f: HOLSequent => Option[LKProof] ): Option[LKProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      applyReplacement( renamedProof, invertRenaming )._1
    }
  }

  private def withGroundVariables2( seq: HOLSequent )( f: HOLSequent => Option[ExpansionSequent] ): Option[ExpansionSequent] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      invertRenaming.foldLeft( renamedProof ) {
        case ( partiallyRenamedProof, ( groundVariable, variable ) ) =>
          partiallyRenamedProof.map( replace( groundVariable.asInstanceOf[FOLConst], variable, _ ) )
      }
    }
  }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    withGroundVariables( seq ) { seq =>
      getRobinsonProof( seq ) map { robinsonProof =>
        RobinsonToLK( robinsonProof, seq )
      }
    }

  override def isValid( seq: HOLSequent ): Boolean =
    getRobinsonProof( groundFreeVariables( seq )._1 ).isDefined

  def getRobinsonProof( seq: HOLSequent ): Option[RobinsonResolutionProof] =
    getRobinsonProof( CNFn.toFClauseList( seq.toFormula ) )

  def getRobinsonProof( seq: Traversable[HOLClause] ): Option[RobinsonResolutionProof]

  override def getExpansionSequent( seq: HOLSequent ): Option[ExpansionSequent] =
    withGroundVariables2( seq ) { seq =>
      getRobinsonProof( seq ).map( RobinsonToExpansionProof( _, seq ) )
    }

}
