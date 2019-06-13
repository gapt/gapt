package gapt.provers.viper.aip.axioms

import gapt.expr.Var
import gapt.formats.tip.{ TipConstructor, TipDatatype }
import gapt.proofs.gaptic.{ ProofState, allR, escargot, forget, induction, orR, repeat }
import gapt.proofs.lk.LKProof
import gapt.proofs.Sequent
import gapt.provers.viper.aip.ThrowsError
import cats.instances.all._
import cats.syntax.all._
import gapt.expr.formula.All
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Or
import gapt.expr.util.freeVariables
import gapt.proofs.LabelledSequent
import gapt.proofs.context.mutable.MutableContext

case class TipDomainClosureAxioms( types: List[TipDatatype] = Nil ) extends AxiomFactory {

  def forTypes( types: TipDatatype* ) = copy( types = types.toList )

  /**
   * Computes domain closure axioms.
   *
   * @param sequent Domain closure axioms are independent of the sequent.
   * @param ctx Defines the constants, types, etc.
   * @return A list of domain closure axioms or an error message if the axioms could not be constructed.
   */
  override def apply( sequent: LabelledSequent )( implicit ctx: MutableContext ): ThrowsError[List[Axiom]] =
    types.traverse[ThrowsError, Axiom] { t =>
      Right( new TipDomainClosureAxiom( t ) )
    }

  private class TipDomainClosureAxiom( datatype: TipDatatype )( implicit ctx: MutableContext ) extends Axiom {
    /**
     * @return The formula representing the axiom.
     */
    override def formula: Formula = {
      val caseVariable = Var( "x", datatype.t )
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
      val All.Block( Seq( variable, _* ), _ ) = formula
      var proofState = ProofState(
        datatype.constructors.flatMap( _.projectorDefinitions ).map( definition => "" -> All.Block( freeVariables( definition ).toSeq, definition ) ) ++:
          Sequent() :+ ( "goal" -> formula ) )
      proofState += allR
      proofState += induction( variable )
      datatype.constructors.foreach { _ =>
        forget( s"IH${variable}_0" )
        proofState += repeat( orR )
        proofState += escargot
      }
      proofState.result
    }

    private def caseDistinction( caseVariable: Var, constructor: TipConstructor ): Formula = {
      val projectedValues = constructor.projectors.map( projector => projector( caseVariable ) )
      Eq( caseVariable, constructor.constr( projectedValues ) )
    }
  }
}

