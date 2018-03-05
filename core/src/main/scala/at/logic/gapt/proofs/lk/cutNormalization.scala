package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.hol.{ containsQuantifier, isAtom }
import at.logic.gapt.expr.{ All, And, Const, Ex, FOLAtom, Formula, Neg, Or, To }
import at.logic.gapt.proofs.{ Context, SequentConnector }
import at.logic.gapt.proofs.lk.reductions._



object inductionEigenvariables {
  /**
    * Retrieves all of the eigenvariables of a given induction rule.
    * @param induction The induction rule.
    * @return All the eigenvariables of the induction rule.
    */
  def apply( induction: InductionRule ) =
    induction.cases.flatMap( _.eigenVars ).toSet
}

object logicalComplexity {
  def apply( formula: Formula ): Int = {
    formula match {
      case PropAtom( _ )        => 0
      case FOLAtom( _, _ )      => 0
      case All( _, subformula ) => 1 + logicalComplexity( subformula )
      case Ex( _, subformula )  => 1 + logicalComplexity( subformula )
      case And( f1, f2 )        => 1 + logicalComplexity( f1 ) + logicalComplexity( f2 )
      case Or( f1, f2 )         => 1 + logicalComplexity( f1 ) + logicalComplexity( f2 )
      case Neg( f1 )            => 1 + logicalComplexity( f1 )
    }
  }

  object PropAtom {
    def unapply( arg: Formula ): Option[String] = {
      arg match {
        case Const( sym, To, _ ) => Some( sym )
        case _                   => None
      }
    }
  }
}


object unfoldInductions {
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof =
    (new IterativeParallelStrategy(inductionUnfoldingReduction, ctx)).run(proof)
}