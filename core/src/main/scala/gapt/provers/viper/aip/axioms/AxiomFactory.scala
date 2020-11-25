package gapt.provers.viper.aip.axioms

import gapt.proofs.LabelledSequent
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.viper.aip.ThrowsError

trait AxiomFactory {
  /**
   * Computes induction axioms for a given sequent.
   *
   * @param sequent The sequent for which the axioms are generated.
   * @param ctx     Defines inductive types etc.
   * @return Either a list of induction axioms or a non empty list of strings describing the why induction axioms
   *         could not be generated.
   */
  def apply( sequent: LabelledSequent )( implicit ctx: MutableContext ): ThrowsError[List[Axiom]]

  final def :/\:( otherFactory: AxiomFactory ): AxiomFactory = new AxiomFactory {
    override def apply( sequent: LabelledSequent )( implicit ctx: MutableContext ): ThrowsError[List[Axiom]] =
      for {
        axiomsLeft <- AxiomFactory.this( sequent )
        axiomsRight <- otherFactory( sequent )
      } yield axiomsLeft ::: axiomsRight
  }
}
