package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.utils.NameGenerator

import scala.util.Random

object randomInstance {

  def generate( tys: Seq[TBase] )( implicit ctx: Context ): Seq[LambdaExpression] = tys.map( generate )
  def generate( ty: TBase )( implicit ctx: Context ): LambdaExpression = generate( ty, new NameGenerator( Set() ) )

  def generate( ty: TBase, nameGen: NameGenerator )( implicit ctx: Context ): LambdaExpression = {
    ctx.typeDef( ty ).get match {
      case Context.Sort( _ ) =>
        Var( nameGen freshWithIndex "x", ty )
      case Context.InductiveType( _, ctrs ) =>
        val ctr = ctrs( Random.nextInt( ctrs.size ) )
        val FunctionType( _, argTypes ) = ctr.exptype
        val args = argTypes map {
          case at: TBase => generate( at, nameGen )
        }
        ctr( args: _* )
    }
  }

  def exprSize( e: LambdaExpression ): Int = e match {
    case _: Var        => 0
    case Apps( _, as ) => 1 + as.map( exprSize ).sum
  }

  def generate( tys: Seq[TBase], cond: Int => Boolean )( implicit ctx: Context ): Seq[LambdaExpression] =
    Stream.continually( generate( tys ) ).filter( insts => cond( insts.map( exprSize ).sum ) ).head

}
