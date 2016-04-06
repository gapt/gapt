package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, FiniteContext }
import at.logic.gapt.utils.NameGenerator

import scala.util.Random

object randomInstance {

  def generateMaxSize( ty: TBase, maxSize: Int, nameGen: NameGenerator )( implicit ctx: Context ): Option[( LambdaExpression, Int )] = {
    ctx.typeDef( ty ).get match {
      case Context.Sort( _ ) =>
        Some( ( Var( nameGen freshWithIndex "x", ty ), 1 ) )
      case Context.InductiveType( _, ctrs ) =>
        val ctr = ctrs( Random.nextInt( ctrs.size ) )
        var maxSize_ = maxSize - 1
        val FunctionType( _, argTypes ) = ctr.exptype
        val args = argTypes map {
          case at: TBase => generateMaxSize( at, maxSize_, nameGen ) match {
            case None => return None
            case Some( ( a, s ) ) =>
              maxSize_ -= s
              ( a, s )
          }
        }
        Some( ( ctr( args.map( _._1 ): _* ), args.map( _._2 ).sum ) )
    }
  }

  def generate( ty: TBase, size: Int )( implicit ctx: Context ): LambdaExpression = {
    generateMaxSize( ty, size, new NameGenerator( Set() ) ) match {
      case Some( ( e, s ) ) if s == size =>
        e
      case _ => generate( ty, size )
    }
  }

  def toSkolemConsts( expr: LambdaExpression, ctx: FiniteContext ): ( LambdaExpression, FiniteContext ) = {
    val nameGen = rename.awayFrom( ctx.constants )

    val vars = freeVariables( expr ).toSeq
    val consts = for ( Var( _, ty @ TBase( name ) ) <- vars ) yield Const( nameGen fresh name, ty )

    ( Substitution( vars zip consts )( expr ), ctx ++ consts )
  }

}
