import gapt.expr.{ Const, Expr, Ty }
import gapt.proofs.Context

package object extraction {
  abstract class CodeGenerator( val name: String ) {

    val prefix: String

    val postfix: String

    def apply( e: Expr )( implicit ctx: Context ) = {
      println( prefix )
      println( generateBoilerPlate( e )( ctx ) )
      println( translate( e )( ctx ) )
      println( postfix )
    }

    def generateBoilerPlate( e: Expr )( implicit ctx: Context ): String

    def toTerm( c: Const ): String

    def toType( t: Ty ): String

    def translate( e: Expr )( implicit ctx: Context ): String
  }
}
