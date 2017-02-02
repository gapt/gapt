package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.Context.{ BaseTypes, StructurallyInductiveTypes }
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable
import cats.syntax.traverse._, cats.instances.list._

object enumerateTerms {
  private def normalizeFreeVars( expr: LambdaExpression ): LambdaExpression = {
    val nameGen = new NameGenerator( Set() )
    def norm( e: LambdaExpression ): LambdaExpression = e match {
      case App( a, b ) => App( norm( a ), norm( b ) )
      case Var( _, t ) => Var( nameGen.freshWithIndex( "x" ), t )
      case c: Const    => c
    }
    norm( expr )
  }
  def asStream( implicit ctx: Context ) = {
    val terms = mutable.Set[LambdaExpression]()

    terms ++= ctx.get[StructurallyInductiveTypes].constructors.values.flatten.filter { _.exptype.isInstanceOf[TBase] }
    terms ++= ( ctx.get[BaseTypes].baseTypes -- ctx.get[StructurallyInductiveTypes].types ).map( Var( "x", _ ) )

    val nonConstantCtrs = ctx.get[StructurallyInductiveTypes].constructors.values.flatten.filterNot { _.exptype.isInstanceOf[TBase] }

    def take( tys: Seq[Ty] ): Seq[Seq[LambdaExpression]] =
      tys.toList.traverse( t => terms.filter( _.exptype == t ).toList )
    def iterate() =
      nonConstantCtrs.flatMap {
        case ctr @ Const( _, FunctionType( _, argTypes ) ) =>
          take( argTypes ).map( ctr( _ ) ).map( normalizeFreeVars )
      }

    ( terms.toVector +: Stream.continually {
      val newTerms = iterate().filterNot( terms )
      terms ++= newTerms
      newTerms
    } ).takeWhile( _.nonEmpty ).flatten
  }
}
