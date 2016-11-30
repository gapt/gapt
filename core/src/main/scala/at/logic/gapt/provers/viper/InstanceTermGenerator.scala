package at.logic.gapt.provers.viper

import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.expr.{ LambdaExpression, TBase }
import at.logic.gapt.proofs.Context

import scala.collection.mutable
import scala.util.Random
import scalaz.Traverse
import scalaz.std.list._

trait InstanceTermGenerator {
  def generate( lower: Float, upper: Float, num: Int ): Set[List[LambdaExpression]]
}
class RandomInstanceGenerator( val paramTys: List[TBase], implicit val ctx: Context ) extends InstanceTermGenerator {
  def generate( lower: Float, upper: Float, num: Int ): Set[List[LambdaExpression]] = {
    var ttl = num * 10
    val instances = mutable.Set[List[LambdaExpression]]()
    while ( instances.size < num && ttl > 0 ) {
      ttl -= 1
      instances += randomInstance.generate( paramTys, x => lower <= x && x <= upper )
    }
    instances.toSet
  }
}
class EnumeratingInstanceGenerator( val paramTys: List[TBase], implicit val ctx: Context ) extends InstanceTermGenerator {
  val terms = enumerateTerms.asStream.take( 10000 ).map( t => t -> folTermSize( t ) )

  override def generate( lower: Float, upper: Float, num: Int ): Set[List[LambdaExpression]] =
    Random.shuffle( Traverse[List].traverse( paramTys )( t =>
      terms.view.filter( _._1.exptype == t ).takeWhile( _._2 <= upper ).toList ).view.
      filter( _.view.map( _._2 ).sum >= lower ).toList ).take( num ).map( _.map( _._1 ) ).toSet
}
