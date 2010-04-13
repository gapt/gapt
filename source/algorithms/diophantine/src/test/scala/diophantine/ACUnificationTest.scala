package at.logic.algorithms.diophantine

import _root_.at.logic.language.hol.logicSymbols.ConstantStringSymbol
import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import org.specs.SpecificationWithJUnit
import at.logic.algorithms.diophantine.Vector
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.fol.{FOLExpression, FOLTerm}

class ACUnificationTest extends SpecificationWithJUnit {
  val parse = (s:String) => (new StringReader(s) with SimpleFOLParser {}).getTerm().asInstanceOf[FOLTerm]
  val f = new ConstantStringSymbol("f")
  def checkResult(subst:Substitution[FOLExpression], t1:FOLTerm, t2:FOLTerm) : Boolean = {
    val term1 = subst.apply(t1)
    val term2 = subst.apply(t2)
    println("")
    println("problem      : "+t1+" =? "+t2)
    println("substitution : "+subst)
    println("checking     : "+term1+" =? "+term2)
    println("")
    true
  }

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
          list must beEqual(r)
        }
      }

    "do normal first order unification" in {
      val term1 = parse("g(a,h(b))")
      val term2 = parse("g(a,b)")
      val term3 = parse("g(x,x)")
      val term4 = parse("g(y,x)")
      val term5 = parse("g(h(x),x)")

      val s12 = ACUnification.unify(f,term1,term2)
      val s13 = ACUnification.unify(f,term1,term3)
      val s14 = ACUnification.unify(f,term1,term4) //unifiable

      val s23 = ACUnification.unify(f,term2,term3)
      val s24 = ACUnification.unify(f,term2,term4) //unifiable

      val s34 = ACUnification.unify(f,term3,term4) //unifiable

      val s35 = ACUnification.unify(f,term3,term5)

      //non unifiable
      (s12,s13,s23,s35) match {
        case (None,None,None,None) => true must beEqual(true)
        case _ => true must beEqual (false)
      }

      (s14, s24,s34) match {
        case (Some(List(r14)), Some(List(r24)),Some(List(r34))) =>
          val tl14 = r14.apply(term1)
          val tr14 = r14.apply(term4)
          val tl24 = r24.apply(term2)
          val tr24 = r24.apply(term4)
          val tl34 = r34.apply(term3)
          val tr34 = r34.apply(term4)

          println(" "+tl14+" "+tr14)
          println(" "+tl24+" "+tr24)
          println(" "+tl34+" "+tr34)

          tl14 must beEqual(tr14)
          tl24 must beEqual(tr24)
          tl34 must beEqual(tr34)
        case _ => true must beEqual (false)
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

      //for (i<- 1 to 1000)
      //  ACUnification unify(f,term1,term2)

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(substs) => true must beEqual (true)
          for (s<-substs) checkResult(s,term1,term2)

        case None => true must beEqual (false)
      }
    }

    "unify f(x,a) = f(y,b)" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(y,b)")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(substs) => true must beEqual (true)
        for (s<-substs) checkResult(s,term1,term2)
        case None => true must beEqual (false)
      }
      ()
    }

    /* */
    "unify f(x,f(a,x)) = f(f(y,a),x)" in {
      val term1 = parse("f(x,f(a,x))")
      val term2 = parse("f(f(x,f(a,a)),y)")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(substs) => true must beEqual (true)
        for (s<-substs) checkResult(s,term1,term2)
        case None => true must beEqual (false)
      }
      ()
    }
    /* */
    "unify f(x,x) = f(y,f(y,y))" in {
      val term1 = parse("f(x,x)")
      val term2 = parse("f(y,f(y,y))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(substs) => true must beEqual (true)
          for (s<-substs) checkResult(s,term1,term2)
        case None => true must beEqual (false)
      }
      ()
    }

    "not unify f(x,g(x)) = f(y,f(y,a))" in {
      val term1 = parse("f(x,g(x))")
      val term2 = parse("f(y,f(y,a))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(substs) => true must beEqual (false)
          for (s<-substs) checkResult(s,term1,term2)
        case None => true must beEqual (true)
      }
      ()
    }

    "not unify f(x,a) = f(y,f(y,g(x)))" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(y,f(y,g(x)))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(substs) => true must beEqual (false)
          for (s<-substs) checkResult(s,term1,term2)
        case None => true must beEqual (true)
      }
      ()
    }

    "unify f(x,f(g(a,b),x)) = f(y,f(y,g(a,u)))" in {
      val term1 = parse("f(x,f(g(a,b),x))")
      val term2 = parse("f(y,f(y,g(a,u)))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu match {
        case Some(substs) => true must beEqual (true)
          for (s<-substs) checkResult(s,term1,term2)
        case None => true must beEqual (false)
      }
      ()
    }

    
  }
}