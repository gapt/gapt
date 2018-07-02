import gapt.expr.{ Const, Expr, Ty }
import gapt.proofs.Context

package object extraction {
  abstract class CodeGenerator {

    def apply( e: Expr )( implicit ctx: Context ) = {
      println( generateBoilerPlate( ctx ) )
      println( translate( e )( ctx ) )
    }

    def generateBoilerPlate( implicit ctx: Context ): String

    def toTerm( c: Const ): String

    def toType( t: Ty ): String

    def translate( e: Expr )( implicit ctx: Context ): String
  }
}
