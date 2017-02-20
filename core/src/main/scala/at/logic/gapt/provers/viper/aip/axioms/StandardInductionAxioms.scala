package at.logic.gapt.provers.viper.aip.axioms
import at.logic.gapt.expr.{ HOLFormula, Substitution, Var, Const => Con }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.provers.viper.aip._
import cats.instances.all._
import cats.syntax.all._

case class StandardInductionAxioms(
    variableSelector: VariableSelector = allVariablesSelector( _ )( _ ),
    formulaSelector:  FormulaSelector  = firstFormulaSelector( _ )
) extends AxiomFactory {

  def forAllVariables = copy( variableSelector = allVariablesSelector( _ )( _ ) )

  def forLabel( label: String ) = copy( formulaSelector = findFormula( _, label ) )

  def forVariables( variables: Var* ) = copy( variableSelector = ( _, _ ) => variables.toList )

  /**
   * Computes induction axioms for a given sequent.
   *
   * @param sequent The sequent for which the axioms are generated.
   * @param ctx     Defines inductive types etc.
   * @return Either a list of induction axioms or a non empty list of strings describing the why induction axioms
   *         could not be generated.
   */
  override def apply( sequent: LabelledSequent )( implicit ctx: Context ): ThrowsError[List[Axiom]] =
    for {
      formula <- formulaSelector( sequent )
      variables = variableSelector( formula, ctx )
      axioms <- variables.traverse[ThrowsError, Axiom]( v => createAxiom( v, formula ) )
    } yield axioms

  /**
   * Creates an induction axiom.
   *
   * @param inductionVariable The variable for which the induction is carried out.
   * @param inductionFormula The formula on which the induction is carried out.
   * @param ctx Specifies constants, types, etc.
   * @return A standard induction axiom for the specified variable and formula.
   */
  private def createAxiom(
    inductionVariable: Var, inductionFormula: HOLFormula
  )( implicit ctx: Context ): ThrowsError[Axiom] = {
    for {
      constructors <- getConstructors( baseType( inductionVariable ), ctx )
    } yield {
      new Axiom {

        val formula = inductionAxiom( inductionVariable, inductionFormula, constructors )

        /**
         * A proof of the validity of this induction axiom.
         * @return An inductive proof of the axiom.
         */
        def proof = {
          val inductiveCaseProofs = constructors map { inductiveCaseProof( _ ) }
          var proofState = ProofState(
            Sequent( Nil, formula :: Nil )
          )
          proofState += repeat( allR )
          proofState += impR
          proofState += allR( inductionVariable )
          proofState += induction( inductionVariable )
          proofState += repeat( andL ).onAllSubGoals
          inductiveCaseProofs foreach {
            proofState += insert( _ )
          }

          proofState.result
        }

        /**
         * Computes proof of the inductive case corresponding to a given constructor.
         * @param constructor The constructor whose associated inductive case is proved.
         * @return A proof of the inductive case associated with the constructor.
         */
        private def inductiveCaseProof( constructor: Con ): LKProof = {
          val inductiveCaseFormula = inductionCase( inductionVariable, inductionFormula, constructor )
          val ( primaryVariables, secondaryVariables, caseConclusion ) =
            inductionCaseConclusion( inductionVariable, constructor, inductionFormula )
          val inductionHypotheses = primaryVariables map {
            primaryVariable => Substitution( inductionVariable -> primaryVariable )( inductionFormula )
          }
          var proofState = ProofState(
            Sequent(
              "icf" -> inductiveCaseFormula ::
                inductionHypotheses.zipWithIndex.map( { case ( hyp, index ) => s"ih$index" -> hyp } ),
              "goal" -> caseConclusion :: Nil
            )
          )
          proofState += allL( "icf", primaryVariables: _* ) orElse skip
          proofState += impL
          if ( primaryVariables.isEmpty )
            proofState += trivial
          else
            primaryVariables foreach {
              _ => proofState += andR andThen trivial orElse trivial
            }
          proofState += allL( secondaryVariables: _* ) orElse skip
          proofState += trivial

          proofState.result
        }
      }
    }
  }
}
