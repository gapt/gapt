package at.logic.algorithms.unification

import _root_.at.logic.algorithms.diophantine.Vector
import _root_.at.logic.language.hol.logicSymbols.ConstantStringSymbol
import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import org.specs.SpecificationWithJUnit
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.fol._
import at.logic.language.lambda.typedLambdaCalculus.Var

class ACUnificationTest extends SpecificationWithJUnit {
  val parse = (s:String) => (new StringReader(s) with SimpleFOLParser {}).getTerm().asInstanceOf[FOLTerm]
  val f = new ConstantStringSymbol("f")
  val debuglevel = 0
  val latex = true

  def striplatex(s:String) = if (latex) s else s.replaceAll("(\\\\|\\$|\\{|\\})","") 
  def debug(l:Int,s:String) = if (l<=debuglevel) println(striplatex(s))

  def printSubst(s:Substitution[FOLTerm]) = {
    for (x <- s.map.toList.sort((x:(Var,FOLExpression), y:(Var,FOLExpression)) => x._1.toString < y._1.toString ) )
      debug(1,"$ "+x._1+" <- "+x._2+" $\\\\")
  }

  def checkResult(substs:Seq[Substitution[FOLTerm]], t1:FOLTerm, t2:FOLTerm) : Boolean = {
    
    debug(1,"")
    debug(1,"\\subsection*{$"+ACUtils.flatten(f,t1) + "=?"  +ACUtils.flatten(f,t2)+"$}")
    //debug(1,"                  ***")
    debug(1,"problem : $"+t1+" =? "+t2+"$\\\\")
    var i = 1
    for (subst <- substs) {
      debug(1,"("+i+")\\\\")
      i = i+1
      val term1 = subst.apply(t1)
      val term2 = subst.apply(t2)
      //debug(1,"substitution      : "+subst)
      printSubst(subst)
      debug(1,"substituted terms     : $" +term1 +" =? "+term2 + "$\\\\")
      debug(1,"substituted rewritten : $"+ACUtils.flatten(f,term1)+" =? "+ACUtils.flatten(f,term2)+"$\\\\")
      ACUtils.flatten(f,term1) must beEqual (ACUtils.flatten(f,term2))
    }
    debug(1,"\\\\")
    //debug(1,"                  ***")
    debug(1,"")
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
          val list = ACUtils nestedFunctions_toList (f,t)
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
      for (i<- List(s12,s13,s23,s35))
        i.length must beEqual (0)

    /*  ((s14, s24,s34) match {
        case (List(r14), List(r24),List(r34)) =>
          val tl14 = r14.apply(term1)
          val tr14 = r14.apply(term4)
          val tl24 = r24.apply(term2)
          val tr24 = r24.apply(term4)
          val tl34 = r34.apply(term3)
          val tr34 = r34.apply(term4)

          tl14 must beEqual(tr14)
          tl24 must beEqual(tr24)
          tl34 must beEqual(tr34)
        case _ => true
      }) must beEqual (false)
      */
    }


    "not unify f(x,a) = f(f(y,a),x)" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(f(x,f(a,a)),y)")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqual (0)
    }
 
    "unify f(x1,x2) = f(f(y1,y2),y3)" in {
      val term1 = parse("f(x_1,x_2)")
      val term2 = parse("f(f(y_1,y_2),y_3)")

      //for (i<- 1 to 1000)
      //  ACUnification unify(f,term1,term2)

      val mgu = ACUnification unify(f,term1,term2)
      (true) must beEqual (mgu.length>0)
      checkResult(mgu,term1,term2)
    }

    "unify f(x,a) = f(y,b)" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(y,b)")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqual (mgu.length>0)
      checkResult(mgu,term1,term2)
      ()
    }

    /* */
    "unify f(x,f(a,x)) = f(f(y,a),x)" in {
      val term1 = parse("f(x,f(a,x))")
      val term2 = parse("f(f(x,f(a,a)),y)")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqual (mgu.length>0)
      checkResult(mgu,term1,term2)
      ()
    }
    /* */
    "unify f(x,x) = f(y,f(y,y))" in {
      val term1 = parse("f(x,x)")
      val term2 = parse("f(y,f(y,y))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqual (mgu.length>0)
      checkResult(mgu,term1,term2)
      ()
    }

    "not unify f(x,g(x)) = f(y,f(y,a))" in {
      val term1 = parse("f(x,g(x))")
      val term2 = parse("f(y,f(y,a))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqual (0)
      ()
    }

    "not unify f(x,a) = f(y,f(y,g(x)))" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(y,f(y,g(x)))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqual (0)
      ()
    }

    "unify f(x,f(g(a,b),x)) = f(y,f(y,g(a,u)))" in {
      val term1 = parse("f(x,f(g(a,b),x))")
      val term2 = parse("f(y,f(y,g(a,u)))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqual (mgu.length>0)
      checkResult(mgu,term1,term2)
      ()
    }

      "unify f(g(f(x, x)), a) = f(u,g(f(y, f(y, y))))" in {
      val term1 = parse("f(g(f(x, x)), a)")
      val term2 = parse("f(u,g(f(y, f(y, y))))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqual (mgu.length>0)
      checkResult(mgu,term1,term2)
      ()
    }

    //this is from the stickel paper
    "unify f(f(x,f(x,y)),f(f(a,b),c)) = f(f(b,b),f(b,f(c,z)))" in {
      val term1 = parse("f(f(x,f(x,y)),f(f(a,b),c))")
      val term2 = parse("f(f(b,b),f(b,f(c,z)))")

      //for (i<-1 to 10000)
      //  ACUnification unify(f,term1,term2)
      TermUtils.generator.reset
      
      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqual (4)
      checkResult(mgu,term1,term2)

      /* test, if subtitution compose is in prefix or postfix notation
      val s = Substitution[FOLExpression]((parse("x").asInstanceOf[FOLVar],parse("y").asInstanceOf[FOLExpression]))
      val t = Substitution[FOLExpression]((parse("y").asInstanceOf[FOLVar],parse("x").asInstanceOf[FOLExpression]))
      val term = parse("f(x,y)")
      debug(1,(s compose t) apply (term))
      debug(1,(t compose s) apply (term))
      */

      ()
    }

    /* */
    "unify f(x,f(y,x)) = f(z,f(z,z))" in {
      val term1 = parse("f(x,f(y,x))")
      val term2 = parse("f(z,f(z,z))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqual (mgu.length>0)
      checkResult(mgu,term1,term2)
      ()
    }

    "unification of syntactically equal terms" in {
      val term1 = parse("f(a,f(b,c))")
      val term2 = parse("f(a,f(b,c))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqual (1)
      mgu(0) must beEqual (Substitution[FOLTerm]())
      
      ()
    }

    "unification of terms with the same number of symbols" in {
      val term1 = parse("f(a,f(g(b),x))")
      val term2 = parse("f(x,f(a,g(b)))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqual (1)
      mgu(0) must beEqual (Substitution[FOLTerm]())
      ()
    }

    "tests for linear independence should work" in {
      val set = List(
          Vector(2,2,2),
          Vector(1,4,2),
          Vector(1,1,1),
          Vector(3,3,3),
          Vector(4,1,3))
      val weight = Vector(2,1,3)
      val v = Vector(2,2,2)
      val w = Vector(3,3,3)
      val x = Vector(3,6,4)

      /*
      true must beEqual (ACUnification.linearlydependent_on(v, set - v ))
      true must beEqual (ACUnification.linearlydependent_on(w, set - v - w ))
      true must beEqual (ACUnification.linearlydependent_on(x, set - v - w - x ))
      */

      val subsumed = ACUtils.removeSubsumedVectors_new(set,Vector(2,1,3))
      true must beEqual (subsumed.length < set.length)

      /*
      val z_1 = Vector(0, 0, 1, 0, 1)
      val z_2 = Vector(0, 1, 0, 0, 1)
      val z_3 = Vector(0, 0, 2, 1, 0)
      val z_4 = Vector(0, 1, 1, 1, 0)
      val z_5 = Vector(0, 2, 0, 1, 0)
      val z_6 = Vector(1, 0, 0, 0, 2)
      val z_7 = Vector(1, 0, 0, 1, 0)

      debug(1,z_4+z_6)
      debug(1,z_2+z_4+z_6)
      debug(1,z_1+z_5+z_6)
      debug(1,z_1+z_2+z_5+z_6)
      debug(1,z_1+z_2+z_7)
      debug(1,z_1+z_2+z_6+z_7)
        */

    }


  }
}
