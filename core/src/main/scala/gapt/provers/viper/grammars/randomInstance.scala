package gapt.provers.viper.grammars

import gapt.expr._
import gapt.expr.fol.folTermSize
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.proofs.context.Context
import gapt.utils.NameGenerator

import scala.util.Random

object randomInstance {

  def generate( tys: Seq[TBase] )( implicit ctx: Context ): Seq[Expr] = {
    val nameGen = new NameGenerator( Set() )
    tys.map( generate( _, nameGen ) )
  }
  def generate( ty: TBase )( implicit ctx: Context ): Expr = generate( ty, new NameGenerator( Set() ) )

  def generate( ty: TBase, nameGen: NameGenerator )( implicit ctx: Context ): Expr = {
    ctx.getConstructors( ty ) match {
      case None =>
        Var( nameGen freshWithIndex "x", ty )
      case Some( ctrs ) =>
        val ctr = ctrs( Random.nextInt( ctrs.size ) )
        val FunctionType( _, argTypes ) = ctr.ty
        val args = argTypes.map { at => generate( at.asInstanceOf[TBase], nameGen ) }
        ctr( args: _* )
    }
  }

  def generate( tys: Seq[TBase], cond: Float => Boolean )( implicit ctx: Context ): Seq[Expr] =
    Stream.continually( generate( tys ) ).filter( insts => cond( folTermSize( insts ).toFloat / insts.size ) ).head

}
