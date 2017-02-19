package at.logic.gapt.provers.viper.aip.axioms

import at.logic.gapt.proofs.Context
import at.logic.gapt.provers.viper.aip.{ ThrowsError, LabelledSequent }

trait AxiomFactory {
  /**
   * Computes induction axioms for a given sequent.
   *
   * @param sequent The sequent for which the axioms are generated.
   * @param ctx     Defines inductive types etc.
   * @return Either a list of induction axioms or a non empty list of strings describing the why induction axioms
   *         could not be generated.
   */
  def apply( sequent: LabelledSequent )( implicit ctx: Context ): ThrowsError[List[Axiom]]

  final def :/\:( otherFactory: AxiomFactory ): AxiomFactory = new AxiomFactory {
    override def apply( sequent: LabelledSequent )( implicit ctx: Context ): ThrowsError[List[Axiom]] =
      for {
        axiomsLeft <- AxiomFactory.this( sequent )
        axiomsRight <- otherFactory( sequent )
      } yield axiomsLeft ::: axiomsRight
  }
}
