/*
 * VariantsDeletionTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import org.specs._
import org.specs.runner._

import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.Definitions._

import VariantsDeletion._

class VariantsDeletionTest extends SpecificationWithJUnit {
  private[subsumption] case class MyVar(nm: String, ta: TA) extends Var(VariableStringSymbol(nm), ta)
  private[subsumption] case class MyConst(nm: String, ta: TA) extends Var(ConstantStringSymbol(nm), ta)

  val vx = MyVar("x",Ti())
  val vy = MyVar("y",Ti())
  val cf = MyConst("f", Ti()->(Ti()->Ti()))
  val vz = MyVar("Z",Ti()->(Ti()->Ti()))
  val ab1 = Abs(vx, AppN(cf, vx::vy::Nil))
  val ab2 = AbsN(vx::vy::Nil, AppN(vz, vx::vy::Nil))
  val ap1 = AppN(ab2, vx::vy::Nil)
  val vy2 = MyVar("y2",Ti())
  val vz2 = MyVar("Z2",Ti()->(Ti()->Ti()))
  val ca = MyConst("a", Ti())

  "VariantsDeletion" should {
    "find that the following are variants of each other" in {
      "1" in {
        (VariantsDeletion.isVariantOf(vx,vy)) must beEqual (true)
      }
      "2" in {
        (VariantsDeletion.isVariantOf(AppN(vz, vx::vy2::Nil),AppN(vz2, vx::vy::Nil))) must beEqual (true)
      }
      "3" in {
        (VariantsDeletion.isVariantOf(AbsN(vx::vy2::Nil, AppN(vz, vx::vy2::Nil)),AbsN(vx::vy::Nil, AppN(vz2, vx::vy::Nil)))) must beEqual (true)
      }
      "4" in {
        (VariantsDeletion.isVariantOf(AppN(AbsN(vx::vy2::Nil, AppN(vz, vx::vy2::Nil)), ca::vy::Nil), AppN(AbsN(vx::vy::Nil, AppN(vz2, vx::vy::Nil)), ca::vy2::Nil))) must beEqual (true)
      }
      "5" in {
        (VariantsDeletion.isVariantOf(App(ab1, AppN(AbsN(vx::vy2::Nil, AppN(vz, vx::vy2::Nil)), ca::vy::Nil)), App(Abs(vx, AppN(cf, vx::vy2::Nil)), AppN(AbsN(vx::vy::Nil, AppN(vz2, vx::vy::Nil)), ca::vy2::Nil)))) must beEqual (true)
      }
    }
    "find that the following are not variants of each other" in {
      "1" in {
        (VariantsDeletion.isVariantOf(vx,ca)) must beEqual (false)
      }
      "2" in {
        (VariantsDeletion.isVariantOf(vx,ca)) must beEqual (false)
      }
    }
  }
}
