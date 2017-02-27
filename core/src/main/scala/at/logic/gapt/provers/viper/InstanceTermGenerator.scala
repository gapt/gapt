package at.logic.gapt.provers.viper

import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.expr.{ LambdaExpression, TBase }
import at.logic.gapt.proofs.Context

import scala.collection.mutable
import scala.util.Random
import cats.instances.list._, cats.syntax.traverse._

trait InstanceTermGenerator {
  def generate( lower: Float, upper: Float, num: Int ): Set[Seq[LambdaExpression]]
}
class RandomInstanceGenerator( val paramTys: Seq[TBase], implicit val ctx: Context ) extends InstanceTermGenerator {
  def generate( lower: Float, upper: Float, num: Int ): Set[Seq[LambdaExpression]] = {
    var ttl = num * 10
    val instances = mutable.Set[Seq[LambdaExpression]]()
    while ( instances.size < num && ttl > 0 ) {
      ttl -= 1
      instances += randomInstance.generate( paramTys, x => lower <= x && x <= upper )
    }
    instances.toSet
  }
}
class EnumeratingInstanceGenerator( val paramTys: Seq[TBase], implicit val ctx: Context ) extends InstanceTermGenerator {
  val terms = enumerateTerms.asStream.take( 10000 ).map( t => t -> folTermSize( t ) )

  override def generate( lower: Float, upper: Float, num: Int ): Set[Seq[LambdaExpression]] =
    Random.shuffle( paramTys.toList.traverse( t =>
      terms.view.filter( _._1.exptype == t ).takeWhile( _._2 <= upper ).toList ).
      filter( _.view.map( _._2 ).sum >= lower ) ).take( num ).map( _.map( _._1 ) ).toSet
}
