package gapt.examples

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Eq
import gapt.expr.formula.FOLFunction
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLVar

/**
 * Contains some commonly used formulas.
 */
object Formulas {
  /**
   *
   * @return A formula expressing the reflexivity of =.
   */
  val ReflexivityEq: FOLFormula = fof"!x x=x"

  /**
   *
   * @return A formula expressing the transitivity of =.
   */
  val TransitivityEq: FOLFormula = fof"!x!y!z (x=y -> y=z -> x=z)"

  /**
   *
   * @return A formula expressing the symmetry of =.
   */
  val SymmetryEq: FOLFormula = fof"!x!y (x=y -> y=x)"

  /**
   *
   * @param f A function symbol.
   * @return A formula expressing that = is a congruence w.r.t. the unary function symbol f.
   */
  def CongUnaryEq( f: String ): FOLFormula = {
    val Seq( x, y ) = safeNames( "=", f )( "x", "y" ) map { FOLVar( _ ) }
    All.Block( Seq( x, y ), Eq( x, y ) --> Eq( FOLFunction( f, x ), FOLFunction( f, y ) ) )
  }

  /**
   *
   * @param f A function symbol.
   * @return A formula expressing that = is a congruence w.r.t. the binary function symbol f.
   */
  def CongBinaryEq( f: String ): FOLFormula = {
    val Seq( x0, x1, y0, y1 ) = safeNames( "=", f )( "x_0", "x_1", "y0", "y_1" ) map { FOLVar( _ ) }
    All.Block( Seq( x0, x1, y0, y1 ), Eq( x0, y0 ) --> ( Eq( x1, y1 ) --> Eq( FOLFunction( f, x0, x1 ), FOLFunction( f, y0, y1 ) ) ) )
  }

  /**
   * Contains definitions related to arithmetic.
   */
  object Peano {
    val zero = FOLConst( "0" )
    val AdditionBase = fof"!x x+0 = x"
    val AdditionSucc = fof"!x!y x + s(y) = s(x+y)"

    val AdditionAssoc = fof"!x!y!z (x+y)+z = x+(y+z)"
  }

  private def safeNames( symbs: String* )( names: String* ): Seq[String] = for ( s <- names ) yield {
    var tmp = s
    while ( symbs contains tmp ) tmp = tmp + "_0"
    tmp
  }
  private def safeName( symbs: String* )( name: String ): String = safeNames( symbs: _* )( name ).head
}
