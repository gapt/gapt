package gapt.proofs.lk.transformations

import gapt.expr.Abs
import gapt.expr.All
import gapt.expr.hol.inductionPrinciple
import gapt.expr.ty.FunctionType
import gapt.proofs.Ant
import gapt.proofs.ProofBuilder
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKVisitor
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.macros.ExchangeRightMacroRule
import gapt.proofs.lk.rules.macros.ForallRightBlock

object makeInductionExplicit {

  def apply( p: LKProof ): LKProof = explicitInductionVisitor( p, () )

  private object explicitInductionVisitor extends LKVisitor[Unit] {

    override def recurse( p: LKProof, otherArg: Unit ): ( LKProof, SequentConnector ) =
      contractAfter( super.recurse )( p, otherArg )

    override def visitInduction( proof: InductionRule, otherArg: Unit ): ( LKProof, SequentConnector ) = {
      val indty = proof.indTy
      val constrs = proof.cases.map { _.constructor }

      val hyps = proof.cases.map { indCase =>
        val constr = indCase.constructor
        val FunctionType( `indty`, argtypes ) = constr.ty
        val vars = indCase.eigenVars

        var p: LKProof = ExchangeRightMacroRule( indCase.proof, indCase.conclusion )
        for ( i <- indCase.hypotheses.reverse )
          p = ImpRightRule( p, indCase.proof.conclusion( i ), p.conclusion.indices.last )

        ForallRightBlock( p, All.Block( vars, p.conclusion.elements.last ), vars )
      }

      val indprin = inductionPrinciple( indty, constrs )

      val hypP = hyps.reduceLeft( ( p, hyp ) =>
        AndRightRule( p, p.conclusion.indices.last,
          hyp, hyp.conclusion.indices.last ) )

      val explicitFOLp =
        ProofBuilder.
          c( LogicalAxiom( proof.mainFormula ) ).
          u( ForallLeftRule( _, Ant( 0 ), All( proof.quant, proof.qfFormula ), proof.term ) ).
          u( ImpLeftRule( hypP, hypP.conclusion.indices.last, _, Ant( 0 ) ) ).
          qed
      val explicitHOLp =
        ForallLeftRule( explicitFOLp, indprin, Abs( proof.quant, proof.qfFormula ) )

      val ( proof_, occConn ) = recurse( explicitHOLp, () )
      ( proof_, occConn * SequentConnector.guessInjection( fromLower = proof.conclusion, toUpper = explicitHOLp.conclusion ).inv )
    }
  }
}
