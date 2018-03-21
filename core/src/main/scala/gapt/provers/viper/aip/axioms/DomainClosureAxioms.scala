package gapt.provers.viper.aip.axioms

import gapt.expr.{ All, Eq, Ex, Formula, FunctionType, Or, TBase, Var, rename, Const => Con }
import gapt.proofs.gaptic.{ ProofState, allR, escargot, induction }
import gapt.proofs.{ Context, MutableContext, Sequent }
import gapt.provers.viper.aip.{ LabelledSequent, ThrowsError, getConstructors }
import cats.instances.all._
import cats.syntax.all._

case class DomainClosureAxioms( types: List[TBase] = Nil ) extends AxiomFactory {

  def forTypes( types: TBase* ) = copy( types = types.toList )

  /**
   * Computes domain closure axioms.
   *
   * @param sequent Domain closure axioms are independent of the sequent.
   * @param ctx Defines the constants, types, etc.
   * @return A list of domain closure axioms or an error message if the axioms could not be constructed.
   */
  override def apply( sequent: LabelledSequent )( implicit ctx: MutableContext ): ThrowsError[List[Axiom]] =
    types.traverse[ThrowsError, Axiom] { t => domainClosureAxiom( t ) }

  /**
   * The domain closure axiom for a given type.
   *
   * @param caseType The type for which the domain closure axiom is created.
   * @param ctx Defines constants, types, etc.
   * @return A domain closure axiom for the specified inductive type or an error message if the given type is
   *         not inductive.
   */
  private def domainClosureAxiom( caseType: TBase )( implicit ctx: MutableContext ): ThrowsError[Axiom] = {
    for {
      constructors <- getConstructors( caseType, ctx )
    } yield new Axiom {
      val formula = domainClosureAxiom( caseType, constructors )
      def proof = {
        var proofState = ProofState( Sequent() :+ formula )
        val All.Block( Seq( variable, _* ), _ ) = formula
        proofState += allR
        proofState += induction( variable )
        constructors foreach {
          _ => proofState += escargot
        }
        proofState.result
      }
    }
  }

  /**
   * The first-order domain closure axiom for a type.
   *
   * @param caseType An inductive type for which the domain closure formula is created.
   * @param constructors Defines constants, types, etc.
   * @return A first-order formula that asserts that the values of the given type are completely represented
   *         by its constructors.
   */
  private def domainClosureAxiom( caseType: TBase, constructors: Seq[Con] ): Formula = {
    val caseVariable = Var( "x", caseType )
    All(
      caseVariable,
      Or( constructors map { constructor => caseDistinction( caseVariable, constructor ) } ) )
  }

  /**
   * A case distinction of the domain closure axiom.
   *
   * @param caseVariable The variable which is to be used for the case distinction.
   * @param constructor The constructor to be used in the case distinction. This constructor must be
   *                    a constructor of the case variable's base type.
   * @return A first-order formula that asserts that x can be represented by the specified constructor.
   */
  private def caseDistinction( caseVariable: Var, constructor: Con ): Formula = {
    val nameGenerator = rename.awayFrom( caseVariable :: Nil )
    val FunctionType( _, argumentTypes ) = constructor.ty
    val newVariables = argumentTypes map {
      argumentType => nameGenerator.fresh( Var( "x", argumentType ) )
    }
    Ex.Block( newVariables, Eq( caseVariable, constructor( newVariables ) ) )
  }

}
