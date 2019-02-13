package gapt

import gapt.expr.subst.FOLSubstitution
import gapt.expr.subst.Substitutable
import gapt.expr.subst.Substitution
import gapt.expr.util.ExpressionParseHelper
import gapt.formats.babel.BabelSignature
import gapt.utils.NameGenerator

package object expr {

  implicit def stringInterpolationForExpressions(
    sc: StringContext )( implicit file: sourcecode.File, line: sourcecode.Line, sig: BabelSignature ) =
    new ExpressionParseHelper( sc, file, line, sig )

  // Type aliases that assert that a type `T` is closed under Substitution and FOLSubstitution, respectively.
  type ClosedUnderSub[T] = Substitutable[Substitution, T, T]
  type ClosedUnderFOLSub[T] = Substitutable[FOLSubstitution, T, T]

  type ClosedUnderReplacement[T] = Replaceable[T, T]

  implicit class ExprNameGenerator( private val nameGen: NameGenerator ) extends AnyVal {
    def fresh( v: Var ): Var = Var( nameGen.fresh( v.name ), v.ty )
    def fresh( v: FOLVar ): FOLVar = FOLVar( nameGen.fresh( v.name ) )
    def fresh( c: Const ): Const = Const( nameGen.fresh( c.name ), c.ty )
    def fresh( c: FOLConst ): FOLConst = FOLConst( nameGen.fresh( c.name ) )
    def fresh( n: VarOrConst ): VarOrConst = n match {
      case v: Var   => fresh( v )
      case c: Const => fresh( c )
    }
  }

  type ReplacementContext = Abs
}
