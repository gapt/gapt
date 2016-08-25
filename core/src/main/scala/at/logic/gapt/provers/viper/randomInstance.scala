package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.proofs.Context
import at.logic.gapt.utils.NameGenerator

import scala.util.Random

object randomInstance {

  def generate( tys: Seq[TBase] )( implicit ctx: Context ): Seq[LambdaExpression] = {
    val nameGen = new NameGenerator( Set() )
    tys.map( generate( _, nameGen ) )
  }
  def generate( ty: TBase )( implicit ctx: Context ): LambdaExpression = generate( ty, new NameGenerator( Set() ) )

  def generate( ty: TBase, nameGen: NameGenerator )( implicit ctx: Context ): LambdaExpression = {
    ctx.typeDef( ty ).get match {
      case Context.Sort( _ ) =>
        Var( nameGen freshWithIndex "x", ty )
      case Context.InductiveType( _, ctrs ) =>
        val ctr = ctrs( Random.nextInt( ctrs.size ) )
        val FunctionType( _, argTypes ) = ctr.exptype
        val args = argTypes.map { at => generate( at.asInstanceOf[TBase], nameGen ) }
        ctr( args: _* )
    }
  }

  def generate( tys: Seq[TBase], cond: Float => Boolean )( implicit ctx: Context ): Seq[LambdaExpression] =
    Stream.continually( generate( tys ) ).filter( insts => cond( folTermSize( insts ).toFloat / insts.size ) ).head

}
