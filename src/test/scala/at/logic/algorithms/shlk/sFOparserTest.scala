/*
 * sFOparserTest.scala
 *
 */

package at.logic.parsing.shlk_parsing

import at.logic.calculi.lk._
import at.logic.language.lambda.types._
import at.logic.language.schema._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.junit.runner.RunWith
import org.specs2.execute.Success
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import scala.io._

@RunWith(classOf[JUnitRunner])
class sFOparserTest extends SpecificationWithJUnit {

  sequential
  "sFOparser" should {

    "parse correctly a FO SLK-proof" in {
      val var3 = Atom(SchemaVar("x3", To),Nil)
      val var4 = Atom(SchemaVar("x4", To),Nil)
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

      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sIND.lks"))

      val map = sFOParser.parseProof(s)

      def f = SchemaConst("f", Ti->Ti)
      def h = SchemaConst("h", ->(Tindex , ->(Ti, Ti)))
      def g = SchemaConst("g", ->(Tindex , ->(Ti, Ti)))
      val k = IntVar("k")
      val x = foVar("x")
      val base2 = x
      val step2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      val base1 = sTerm(g, IntZero(), x::Nil)
      val step1 = sTerm(g, Succ(k), x::Nil)
      dbTRS.clear
      dbTRS.add(g, Tuple2(base1, base2), Tuple2(step1, step2))
      Success()

    }


    "parse correctly the journal example" in {

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
      val f1 = And(A0, BigAnd(i,Ai,IntZero(),Succ(i)))
      val ax11 = Axiom(A0::Nil, A0::Nil)

      val s = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("shlk-journal_example.lks"))

      val map = sFOParser.parseProof(s)

      def f = SchemaConst("f", Ti->Ti)
      def h = SchemaConst("h", ->(Tindex , ->(Ti, Ti)))
      def g = SchemaConst("g", ->(Tindex , ->(Ti, Ti)))
      val k = IntVar("k")
      val x = foVar("x")
      val base2 = x
      val step2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      val base1 = sTerm(g, IntZero(), x::Nil)
      val step1 = sTerm(g, Succ(k), x::Nil)
      dbTRS.clear
      dbTRS.add(g, Tuple2(base1, base2), Tuple2(step1, step2))

      Success()

    }
  }
}


