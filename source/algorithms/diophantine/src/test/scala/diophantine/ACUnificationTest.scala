package diophantine

import _root_.at.logic.language.fol.FOLTerm
import _root_.at.logic.language.hol.logicSymbols.ConstantStringSymbol
import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import org.specs.SpecificationWithJUnit
import at.logic.algorithms.diophantine.Vector

class ACUnificationTest extends SpecificationWithJUnit {
  val parse = (s:String) => (new StringReader(s) with SimpleFOLParser {}).getTerm().asInstanceOf[FOLTerm]
  val f = new ConstantStringSymbol("f")

  "AC Unification" should {
      "rewrite terms correctly" in {
        val terms = List("f(f(x,y),f(x,y))",
                        "f(g(x,y),f(x,y))",
                        "f(f(a,y),f(b,y))",
                        "f(f(a,f(s,y)),f(f(u,v),y))"
          ) map parse

        val results = List(
          List("x","y","x","y"),
          List("g(x,y)","x","y"),
          List("a","y","b","y"),
          List("a","s","y","u","v","y")
          ) map (_ map parse)

        for ((t,r) <- terms zip results) {
          val list = ACUnification nestedFunctions_toList (f,t)
          /*println(list)
            println(r)*/
          list must beEqual(r)
        }
      }

    "not unify f(x,a) = f(f(y,a),x)" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(f(x,f(a,a)),y)")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(_) => true must beEqual (false)
        case None => true must beEqual (true)
      }
    }

    "unify f(x1,x2) = f(f(y1,y2),y3)" in {
      val term1 = parse("f(x1,x2)")
      val term2 = parse("f(f(y1,y2),y3)")

      for (i<- 1 to 1000)
        ACUnification unify(f,term1,term2)

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(_) => true must beEqual (true)
        case None => true must beEqual (false)
      }
    }

    /* */
    "unify f(x,f(a,x)) = f(f(y,a),x)" in {
      val term1 = parse("f(x,f(a,x))")
      val term2 = parse("f(f(x,f(a,a)),y)")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(subst) => true must beEqual (true)
        case None => true must beEqual (false) 
      }
      ()
    }
    /* */

  }
}