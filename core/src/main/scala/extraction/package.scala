import gapt.expr.{ Const, Expr, Ty }
import gapt.proofs.context.Context

package object extraction {
  abstract class CodeGenerator( val name: String ) {

    val prefix: String

    val postfix: String

    def apply( e: Expr )( implicit ctx: Context ): String =
      List( prefix, generateBoilerPlate( e )( ctx ), translate( e )( ctx ), postfix ).mkString( "\n" )

    def generateBoilerPlate( e: Expr )( implicit ctx: Context ): String

    def toTerm( c: Const ): String

    def toType( t: Ty ): String

    def translate( e: Expr )( implicit ctx: Context ): String
  }
}
