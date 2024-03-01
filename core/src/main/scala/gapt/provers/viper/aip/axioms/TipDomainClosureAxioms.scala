package gapt.provers.viper.aip.axioms

import cats.instances.all._
import cats.syntax.all._
import gapt.expr.Var
import gapt.expr.formula.All
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Or
import gapt.expr.util.freeVariables
import gapt.logic.projectorDefinitions
import gapt.proofs.LabelledSequent
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.InductiveType.Constructor
import gapt.proofs.gaptic.ProofState
import gapt.proofs.gaptic.allR
import gapt.proofs.gaptic.escargot
import gapt.proofs.gaptic.forget
import gapt.proofs.gaptic.induction
import gapt.proofs.gaptic.orR
import gapt.proofs.gaptic.repeat
import gapt.proofs.lk.LKProof
import gapt.provers.viper.aip.ThrowsError

case class TipDomainClosureAxioms( types: List[InductiveType] = Nil ) extends AxiomFactory {

  def forTypes( types: InductiveType* ) = copy( types = types.toList )

  /**
   * Computes domain closure axioms.
   *
   * @param sequent Domain closure axioms are independent of the sequent.
   * @param ctx Defines the constants, types, etc.
   * @return A list of domain closure axioms or an error message if the axioms could not be constructed.
   */
  override def apply( sequent: LabelledSequent )( implicit ctx: Context ): ThrowsError[List[Axiom]] =
    types.traverse[ThrowsError, Axiom] { t =>
      Right( new TipDomainClosureAxiom( t ) )
    }

  private class TipDomainClosureAxiom( datatype: InductiveType )( implicit ctx: Context ) extends Axiom {
    /**
     * @return The formula representing the axiom.
     */
    override def formula: Formula = {
      val caseVariable = Var( "x", datatype.baseType )
      All(
        caseVariable,
        Or( datatype.constructors map {
          caseDistinction( caseVariable, _ )
        } ) )
    }

    /**
     * @return A proof of the axiom.
     */
    override def proof: LKProof = {
      val All.Block( Seq( variable, _* ), _ ) = formula: @unchecked
      var proofState = ProofState(
        projectorDefinitions( datatype ).map( definition => "" -> All.Block( freeVariables( definition ).toSeq, definition ) ) ++:
          Sequent() :+ ( "goal" -> formula ) )
      proofState += allR
      proofState += induction( variable )
      datatype.constructors.foreach { _ =>
        forget( s"IH${variable}_0" )
        proofState += repeat( orR )
        proofState += escargot( ctx.newMutable )
      }
      proofState.result
    }

    private def caseDistinction( caseVariable: Var, constructor: Constructor ): Formula = {
      val projectedValues = constructor.fields.map {
        f =>
          val p = f.projector.get
          p( caseVariable )
      }
      Eq( caseVariable, constructor.constant( projectedValues ) )
    }
  }
}

