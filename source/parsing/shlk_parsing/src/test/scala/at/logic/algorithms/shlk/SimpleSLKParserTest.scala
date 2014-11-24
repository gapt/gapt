/*
 * SimpleHOLParser.scala
 *
 */

package at.logic.parsing.shlk_parsing

import at.logic.language.schema._
import at.logic.calculi.lk._
import at.logic.language.lambda.types.To

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import scala.io._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success
import at.logic.language.schema._

@RunWith(classOf[JUnitRunner])
class SimpleSLKParserTest extends SpecificationWithJUnit {
    "SimpleSLKParser" should {

      sequential
        "parse correctly a SLK-proof" in {
          val var3 = Atom(SchemaVar("x3",To), Nil)
          val var4 = Atom(SchemaVar("x4",To), Nil)
          val ax1  = Axiom(var3::Nil, var3::Nil)
          val ax2  = Axiom(var4::Nil, var4::Nil)
          val negl = NegLeftRule(ax1, var3)
          val proof  = OrLeftRule(negl, ax2, var3, var4)

          val A0 = IndexedPredicate("A", IntZero())
          val i = IntVar("i")
          val Ai2 = IndexedPredicate("A", Succ(Succ(i)))
          val Ai = IndexedPredicate("A", Succ(i))
          val f1 = at.logic.language.schema.And(A0, BigAnd(i,Ai,IntZero(),Succ(i)))
          val ax11 = Axiom(A0::Nil, A0::Nil)

          val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("shlk-adder.lks"))

          val map = SHLK.parseProof(s)

          Success()

        }
    }
}
