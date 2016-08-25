package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable
import scalaz.Traverse
import scalaz.std.list._

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

    terms ++= ctx.elements.collect { case InductiveType( _, ctrs ) => ctrs.filter { _.exptype.isInstanceOf[TBase] } }.flatten
    terms ++= ctx.elements.collect { case Sort( ty ) => Var( "x", ty ) }

    val nonConstantCtrs = ctx.elements.collect { case InductiveType( _, ctrs ) => ctrs.filterNot { _.exptype.isInstanceOf[TBase] } }.flatten

    def take( tys: Seq[Ty] ): Seq[Seq[LambdaExpression]] =
      Traverse[List].traverse( tys.toList )( t => terms.filter( _.exptype == t ).toList )
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
