package gapt.provers.viper.grammars

import gapt.expr.formula.fol.folTermSize
import gapt.expr.Expr
import cats.instances.list._
import cats.syntax.traverse._
import gapt.expr.ty.TBase
import gapt.expr.ty.Ty
import gapt.proofs.context.Context

import scala.collection.mutable
import scala.util.Random

trait InstanceTermGenerator {
  def generate(lower: Float, upper: Float, num: Int): Set[Seq[Expr]]
}
class RandomInstanceGenerator(val paramTys: Seq[TBase], implicit val ctx: Context) extends InstanceTermGenerator {
  def generate(lower: Float, upper: Float, num: Int): Set[Seq[Expr]] = {
    var ttl = num * 10
    val instances = mutable.Set[Seq[Expr]]()
    while (instances.size < num && ttl > 0) {
      ttl -= 1
      instances += randomInstance.generate(paramTys, x => lower <= x && x <= upper)
    }
    instances.toSet
  }
}
class EnumeratingInstanceGenerator(val paramTys: Seq[Ty], val freeConstructors: Boolean, implicit val ctx: Context) extends InstanceTermGenerator {
  val terms = enumerateTerms.forType(freeConstructors, paramTys: _*).take(10000).map(t => t -> folTermSize(t))

  override def generate(lower: Float, upper: Float, num: Int): Set[Seq[Expr]] =
    if (paramTys.isEmpty) Set(Seq())
    else
      Random.shuffle(paramTys.toList.traverse(t =>
        terms.view.filter(_._1.ty == t).takeWhile(_._2 <= upper).toList
      ).filter(_.view.map(_._2).sum >= lower)).take(num).map(_.map(_._1)).toSet
}
