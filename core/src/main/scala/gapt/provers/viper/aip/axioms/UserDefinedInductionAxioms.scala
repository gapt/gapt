package gapt.provers.viper.aip.axioms

import gapt.expr._
import gapt.proofs.gaptic.OpenAssumption
import gapt.proofs.Sequent
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.viper.aip.ThrowsError

case class UserDefinedInductionAxioms( axioms: List[String] ) extends AxiomFactory {
  /**
   * Returns user defined induction axioms.
   *
   * @param ctx Defines inductive types etc.
   * @return Either a list of induction axioms or a non empty list of strings describing why induction axioms
   *         could not be generated.
   */
  override def apply( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): ThrowsError[List[Axiom]] =
    try {
      Right(
        axioms map { s =>
          new Axiom() {
            val formula = StringContext( s ).hof( s )
            val proof = new OpenAssumption( Sequent() :+ ( "" -> formula ) )
          }
        } )
    } catch {
      case e: IllegalArgumentException => Left( e.getMessage() )
    }
}
