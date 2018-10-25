package gapt.provers.viper.grammars

import cats.instances.list._
import cats.syntax.traverse._
import gapt.expr._
import gapt.proofs.context.Context
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.utils.NameGenerator

import scala.collection.mutable

object enumerateTerms {
  private def normalizeFreeVars( expr: Expr ): Expr = {
    val nameGen = new NameGenerator( Set() )
    def norm( e: Expr ): Expr = e match {
      case App( a, b ) => App( norm( a ), norm( b ) )
      case Var( _, t ) => Var( nameGen.freshWithIndex( "x" ), t )
      case c: Const    => c
    }
    norm( expr )
  }
  def asStream( implicit ctx: Context ) = {
    val terms = mutable.Set[Expr]()

    terms ++= ctx.get[StructurallyInductiveTypes].constructors.values.flatten.filter { _.ty.isInstanceOf[TBase] }
    terms ++= ( ctx.get[BaseTypes].baseTypes -- ctx.get[StructurallyInductiveTypes].constructors.keySet ).values.map( Var( "x", _ ) )

    val nonConstantCtrs = ctx.get[StructurallyInductiveTypes].constructors.values.flatten.filterNot { _.ty.isInstanceOf[TBase] }

    def take( tys: Seq[Ty] ): Seq[Seq[Expr]] =
      tys.toList.traverse( t => terms.filter( _.ty == t ).toList )
    def iterate() =
      nonConstantCtrs.flatMap {
        case ctr @ Const( _, FunctionType( _, argTypes ), _ ) =>
          take( argTypes ).map( ctr( _ ) ).map( normalizeFreeVars )
      }

    ( terms.toVector +: Stream.continually {
      val newTerms = iterate().filterNot( terms )
      terms ++= newTerms
      newTerms
    } ).takeWhile( _.nonEmpty ).flatten
  }
}
