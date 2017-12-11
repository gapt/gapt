package at.logic.gapt.provers.viper.aip.axioms

import at.logic.gapt.expr.{ All, Eq, Formula, Or, Var, freeVariables }
import at.logic.gapt.formats.tip.{ TipConstructor, TipDatatype }
import at.logic.gapt.proofs.gaptic.{ ProofState, allR, escargot, forget, induction, orR, repeat }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, MutableContext, Sequent }
import at.logic.gapt.provers.viper.aip.{ LabelledSequent, ThrowsError }
import cats.instances.all._
import cats.syntax.all._

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

