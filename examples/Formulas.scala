package at.logic.gapt.examples

import at.logic.gapt.expr._
/**
 * Created by sebastian on 2/16/16.
 */

/**
 * Contains some commonly used formulas.
 */
object Formulas {
  /**
   *
   * @param rel A relation symbol
   * @return A formula expressing the reflexivity of rel.
   */
  def Reflexivity( rel: String ): FOLFormula = {
    val x = FOLVar( safeName( rel )( "x" ) )
    All( x, FOLAtom( rel, x, x ) )
  }

  /**
   *
   * @return A formula expressing the reflexivity of =.
   */
  def ReflexivityEq: FOLFormula = Reflexivity( "=" )

  /**
   *
   * @param rel A relation symbol
   * @return A formula expressing the transitivity of rel.
   */
  def Transitivity( rel: String ): FOLFormula = {
    val Seq( x, y, z ) = safeNames( rel )( "x", "y", "z" ) map { FOLVar( _ ) }
    All.Block( Seq( x, y, z ), FOLAtom( rel, x, y ) --> ( FOLAtom( rel, y, z ) --> FOLAtom( rel, x, z ) ) )
  }

  /**
   *
   * @return A formula expressing the transitivity of =.
   */
  def TransitivityEq: FOLFormula = Transitivity( "=" )

  /**
   *
   * @param rel A relation symbol
   * @return A formula expressing the symmetry of rel.
   */
  def Symmetry( rel: String ): FOLFormula = {
    val Seq( x, y ) = safeNames( rel )( "x", "y" ) map { FOLVar( _ ) }
    All.Block( Seq( x, y ), FOLAtom( rel, x, y ) --> FOLAtom( rel, y, x ) )
  }

  /**
   *
   * @return A formula expressing the symmetry of =.
   */
  def SymmetryEq: FOLFormula = Symmetry( "=" )

  /**
   *
   * @param rel A relation symbol.
   * @param f A function symbol.
   * @return A formula expressing that rel is a congruence w.r.t. the unary function symbol f.
   */
  def CongUnary( rel: String, f: String ): FOLFormula = {
    require( f != rel, "Cannot use same symbol for relation and function" )

    val Seq( x, y ) = safeNames( rel, f )( "x", "y" ) map { FOLVar( _ ) }

    All.Block( Seq( x, y ), FOLAtom( rel, x, y ) --> FOLAtom( rel, FOLFunction( f, x ), FOLFunction( f, y ) ) )
  }

  /**
   *
   * @param f A function symbol.
   * @return A formula expressing that = is a congruence w.r.t. the unary function symbol f.
   */
  def CongUnaryEq( f: String ): FOLFormula = CongUnary( "=", f )

  /**
   *
   * @param rel A relation symbol
   * @param f A function symbol.
   * @return A formula expressing that rel is a congruence w.r.t. the binary function symbol f.
   */
  def CongBinary( rel: String, f: String ): FOLFormula = {
    require( f != rel, "Cannot use same symbol for relation and function" )

    val Seq( x0, x1, y0, y1 ) = safeNames( rel, f )( "x_0", "x_1", "y0", "y_1" ) map { FOLVar( _ ) }

    All.Block( Seq( x0, x1, y0, y1 ), FOLAtom( rel, x0, y0 ) --> ( FOLAtom( rel, x1, y1 ) --> FOLAtom( rel, FOLFunction( f, x0, x1 ), FOLFunction( f, y0, y1 ) ) ) )
  }

  /**
   *
   * @param f A function symbol.
   * @return A formula expressing that = is a congruence w.r.t. the binary function symbol f.
   */
  def CongBinaryEq( f: String ): FOLFormula = CongBinary( "=", f )

  /**
   * Contains definitions related to arithmetic.
   */
  object Peano {
    val zero = FOLConst( "0" )
    val AdditionBase = p9f"(all x x+0 = x)"
    val AdditionSucc = p9f"(all x all y x + s(y) = s(x+y))"

    val AdditionAssoc = p9f"(all x all y all z (x + y) + z = x + (y + z))"
  }

  private def safeNames( symbs: String* )( names: String* ): Seq[String] = for ( s <- names ) yield {
    var tmp = s
    while ( symbs contains tmp ) tmp = tmp + "_0"
    tmp
  }
  private def safeName( symbs: String* )( name: String ): String = safeNames( symbs: _* )( name ).head
}
