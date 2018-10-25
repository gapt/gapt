package gapt.provers.viper

import gapt.expr.{ Formula, TBase, Var, Const => Con }
import gapt.formats.tip.TipProblem
import gapt.proofs.context.Context
import gapt.proofs.{ Ant, Sequent }

package object aip {

  type ThrowsError[T] = Either[String, T]
  type LabelledSequent = Sequent[( String, Formula )]

  /**
   * Checks whether the given variable has is of inductive type in the given context.
   *
   * @param v   The variable for which to check the type.
   * @param ctx The context w.r.t. to which the variable's type is checked.
   * @return Returns true if the variable v is of inductive type in the context ctx, false otherwise.
   */
  def hasInductiveType( v: Var )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( v.ty ).isDefined

  /**
   * Converts a TIP problem to sequent with context.
   *
   * @param problem The TIP problem to be converted to a sequent.
   * @return A labelled sequent whose formulas of the antecedent are labelled "h<i>" where i = 1,2,..., and whose
   *         unique formula in the succedent is labelled "goal". Moreover a context specifying the constants and
   *         types, etc. is returned.
   */
  def tipProblemToSequent( problem: TipProblem ): ( Sequent[( String, Formula )], Context ) =
    (
      problem.toSequent.zipWithIndex.map {
        case ( f, Ant( i ) ) => s"h$i" -> f
        case ( f, _ )        => "goal" -> f
      },
      problem.ctx )

  /**
   * Reads the constructors of type `typ` from the context.
   *
   * @param typ A base type.
   * @return Either a list containing the constructors of `typ` or a TacticalFailure.
   */
  def getConstructors(
    typ: TBase, ctx: Context ): ThrowsError[List[Con]] =
    ( ctx.isType( typ ), ctx.getConstructors( typ ) ) match {
      case ( true, Some( constructors ) ) => Right( constructors.toList )
      case ( true, None )                 => Left( s"Type $typ is not inductively defined" )
      case ( false, _ )                   => Left( s"Type $typ is not defined" )
    }

  /**
   * Retrieves the base type of a variable.
   *
   * @param variable A variable.
   * @return The variable's base type.
   */
  def baseType( variable: Var ): TBase = variable.ty.asInstanceOf[TBase]

  /**
   * Finds a formula by label in a labelled sequent.
   *
   * @param sequent The sequent in which to search for the given label.
   * @param label   The formula's label.
   * @return The formula designated by the given label or an error message if the formula
   *         is not be uniquely determined by the label.
   */
  def findFormula( sequent: Sequent[( String, Formula )], label: String ): ThrowsError[Formula] = {
    sequent.succedent filter { case ( l, f ) => l == label } match {
      case Vector( lf ) => Right( lf._2 )
      case lf +: _      => Left( "Formula could not be uniquely determined" )
      case _            => Left( s"Label $label not found" )
    }
  }
}
