package at.logic.gapt

import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.utils.NameGenerator

package object expr {

  implicit def stringInterpolationForExpressions(
    sc: StringContext
  )( implicit file: sourcecode.File, line: sourcecode.Line, sig: BabelSignature ) =
    new ExpressionParseHelper( sc, file, line, sig )

  // Type aliases that assert that a type `T` is closed under Substitution and FOLSubstitution, respectively.
  type ClosedUnderSub[T] = Substitutable[Substitution, T, T]
  type ClosedUnderFOLSub[T] = Substitutable[FOLSubstitution, T, T]

  implicit class ExprNameGenerator( private val nameGen: NameGenerator ) extends AnyVal {
    def fresh( v: Var ): Var = Var( nameGen.fresh( v.name ), v.exptype )
    def fresh( v: FOLVar ): FOLVar = FOLVar( nameGen.fresh( v.name ) )
    def fresh( c: Const ): Const = Const( nameGen.fresh( c.name ), c.exptype )
    def fresh( c: FOLConst ): FOLConst = FOLConst( nameGen.fresh( c.name ) )
    def fresh( n: VarOrConst ): VarOrConst = n match {
      case v: Var   => fresh( v )
      case c: Const => fresh( c )
    }
  }
}
