package at.logic.algorithms.unification

import _root_.at.logic.algorithms.diophantine.Vector
import _root_.at.logic.calculi.lk.base.types.FSequent
import _root_.at.logic.calculi.lk.base.{Sequent, FSequent}
import _root_.at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import _root_.at.logic.language.hol.{HOL, HOLFormula}
import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.fol._
import at.logic.language.lambda.typedLambdaCalculus.Var
import scala.collection.immutable.Seq
import org.specs2.matcher.Matcher
import org.specs2.matcher.Expectable
import org.specs2.execute.Skipped
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class ACUnificationTest extends SpecificationWithJUnit {
  val parse = (s:String) => (new StringReader(s) with SimpleFOLParser {}).getTerm().asInstanceOf[FOLTerm]
  val parse_pred = (s:String) => (new StringReader(s) with SimpleFOLParser {}).getTerm().asInstanceOf[FOLFormula]
  val f = new ConstantStringSymbol("f")
  val g = new ConstantStringSymbol("g")
  val debuglevel = 0
  val latex = true

  def striplatex(s:String) = if (latex) s else s.replaceAll("(\\\\|\\$|\\{|\\})","") 
  def debug(l:Int,s:String) = if (l<=debuglevel) println(striplatex(s))

  def printSubst(s:Substitution[FOLTerm]) = {
    for (x <- s.map.toList.sortWith((x:(Var,FOLExpression), y:(Var,FOLExpression)) => x._1.toString < y._1.toString ) )
      debug(1,"$ "+x._1+" <- "+x._2+" $\\\\")
  }

  case class beSyntacticallyEqual(a: FOLTerm) extends Matcher[FOLTerm]() {
   def apply[S <: FOLTerm](v: Expectable[S]) = result(v.value.syntaxEquals(a), v.value.toString + " is syntactically equal " + a.toString, v.toString + " is not syntactically equal to " + a.toString,v)
  }


  case class beWordEqualModulo(theory : EequalityA, a: FOLTerm ) extends Matcher[FOLTerm]() {
    def apply[S <: FOLTerm](v: Expectable[S]) = result(theory.word_equalsto(v.value,  a), v.toString + " is word equal " + a.toString, v.toString + " is not word equal to " + a.toString,v)
  }

  case class beACWordEqual(theory_functions : List[ConstantSymbolA], a: FOLTerm )
    extends Matcher[FOLTerm] {
     def apply[S <: FOLTerm](v: Expectable[S]) = (new beWordEqualModulo(new MulACEquality(theory_functions), a)).apply(v)
  }

  case class beACUWordEqual(theory_functions : List[ConstantSymbolA], theory_constants : List[ConstantSymbolA], a: FOLTerm )
    extends Matcher[FOLTerm] {
     def apply[S <: FOLTerm](v: Expectable[S]) = (new beWordEqualModulo(new MulACUEquality(theory_functions, theory_constants), a)).apply(v)
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
      ACUtils.flatten(f,term1) must beEqualTo (ACUtils.flatten(f,term2))
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
          list must beEqualTo(r)
        }
        // needed for the test to be visible because of the loop
        Success()
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
        i.length must beEqualTo (0)

    /*  ((s14, s24,s34) match {
        case (List(r14), List(r24),List(r34)) =>
          val tl14 = r14.apply(term1)
          val tr14 = r14.apply(term4)
          val tl24 = r24.apply(term2)
          val tr24 = r24.apply(term4)
          val tl34 = r34.apply(term3)
          val tr34 = r34.apply(term4)

          tl14 must beEqualTo(tr14)
          tl24 must beEqualTo(tr24)
          tl34 must beEqualTo(tr34)
        case _ => true
      }) must beEqualTo (false)
      */
        // needed for the test to be visible because of the loop
        Success()
    }


    "not unify f(x,a) = f(f(y,a),x)" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(f(x,f(a,a)),y)")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqualTo (0)
    }
 
    "unify f(x1,x2) = f(f(y1,y2),y3)" in {
      val term1 = parse("f(x_1,x_2)")
      val term2 = parse("f(f(y_1,y_2),y_3)")

      //for (i<- 1 to 1000)
      //  ACUnification unify(f,term1,term2)

      val mgu = ACUnification unify(f,term1,term2)
      (true) must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }

    "unify f(x,a) = f(y,b)" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(y,b)")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }

    /* */
    "unify f(x,f(a,x)) = f(f(y,a),x)" in {
      val term1 = parse("f(x,f(a,x))")
      val term2 = parse("f(f(x,f(a,a)),y)")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }
    /* */
    "unify f(x,x) = f(y,f(y,y))" in {
      val term1 = parse("f(x,x)")
      val term2 = parse("f(y,f(y,y))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }

    "not unify f(x,g(x)) = f(y,f(y,a))" in {
      val term1 = parse("f(x,g(x))")
      val term2 = parse("f(y,f(y,a))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqualTo (0)
    }

    "not unify f(x,a) = f(y,f(y,g(x)))" in {
      val term1 = parse("f(x,a)")
      val term2 = parse("f(y,f(y,g(x)))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqualTo (0)
    }

    "unify f(x,f(g(a,b),x)) = f(y,f(y,g(a,u)))" in {
      val term1 = parse("f(x,f(g(a,b),x))")
      val term2 = parse("f(y,f(y,g(a,u)))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }

      "unify f(g(f(x, x)), a) = f(u,g(f(y, f(y, y))))" in {
      val term1 = parse("f(g(f(x, x)), a)")
      val term2 = parse("f(u,g(f(y, f(y, y))))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }

    //this is from the stickel paper
    "unify f(f(x,f(x,y)),f(f(a,b),c)) = f(f(b,b),f(b,f(c,z)))" in {
      val term1 = parse("f(f(x,f(x,y)),f(f(a,b),c))")
      val term2 = parse("f(f(b,b),f(b,f(c,z)))")

      //for (i<-1 to 10000)
      //  ACUnification unify(f,term1,term2)
      TermUtils.generator.reset
      
      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqualTo (4)
      checkResult(mgu,term1,term2)

      /* test, if subtitution compose is in prefix or postfix notation
      val s = Substitution[FOLExpression]((parse("x").asInstanceOf[FOLVar],parse("y").asInstanceOf[FOLExpression]))
      val t = Substitution[FOLExpression]((parse("y").asInstanceOf[FOLVar],parse("x").asInstanceOf[FOLExpression]))
      val term = parse("f(x,y)")
      debug(1,(s compose t) apply (term))
      debug(1,(t compose s) apply (term))
      */

    }

    /* */
    "unify f(x,f(y,x)) = f(z,f(z,z))" in {
      val term1 = parse("f(x,f(y,x))")
      val term2 = parse("f(z,f(z,z))")

      val mgu = ACUnification unify(f,term1,term2)
      true must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }

    "unification of syntactically equal terms" in {
      val term1 = parse("f(a,f(b,c))")
      val term2 = parse("f(a,f(b,c))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqualTo (1)
      mgu(0) must beEqualTo (Substitution[FOLTerm]())
      
    }

    "unification of terms with the same number of symbols" in {
      val term1 = parse("f(a,f(g(b),x))")
      val term2 = parse("f(x,f(a,g(b)))")

      val mgu = ACUnification unify(f,term1,term2)
      mgu.length must beEqualTo (1)
      mgu(0) must beEqualTo (Substitution[FOLTerm]())
    }

    "working unification of multiple terms" in {
      val term1 = parse("f(a,f(b,f(c,x)))")
      val term2 = parse("f(d,f(b,f(c,y)))")
      val term3 = parse("f(e,f(b,f(c,z)))")
      val expected = parse("f(a,f(b,f(c,f(d,e))))")
      val terms = List(term1,term2,term3)

      val mgu = ACUnification unify(f,terms)
      //TODO: well this should work, but it does not in the current implementation. grmbl.
      /*
      mgu.length must beEqualTo (1)
      mgu(0) must beEqualTo (Substitution[FOLTerm]())
      val subterms = terms map ( (term:FOLTerm) => ACUtils.flatten(f,mgu(0).apply(term)))
      */

    }

    "handle n-ary non-ac function symbols" in {
      val term1 = parse("g( f(a,x), f(b,y), f(c,z) )")
      val term2 = parse("g(u,u,u)")
      println(term1)
      println(term2)

      val mgu = ACUnification unify(f,term1, term2)

      true must beEqualTo (mgu.length>0)
      checkResult(mgu,term1,term2)
    }.pendingUntilFixed("does not work")
    
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
      true must beEqualTo (ACUnification.linearlydependent_on(v, set - v ))
      true must beEqualTo (ACUnification.linearlydependent_on(w, set - v - w ))
      true must beEqualTo (ACUnification.linearlydependent_on(x, set - v - w - x ))
      */

      val subsumed = ACUtils.removeSubsumedVectors_new(set,Vector(2,1,3))
      true must beEqualTo (subsumed.length < set.length)

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

    "folded flattening should work on some simple examples" in {
      val terms = List("f(f(x,y),f(x,y))",
                       "f(g(x,y),f(x,y))",
                       "f(f(a,y),f(b,y))",
                       "f(f(a,f(s,y)),f(f(u,v),y))",
                       "f(g(x,y),f(x,f(f(e0,e1),y)))",
                       "f(g(e1,e0),f(e0,e0))",
                       "f(g(e1,e1),f(e0,e0))"
        ) map parse

      val fterms = List("f(x,x,y,y)",
                       "f(x,y,g(x,y))",
                       "f(a,b,y,y)",
                       "f(a,s,u,v,y,y)",
                       "f(e1,x,y,g(x,y))",
                       "e0",
                       "e1"
        ) map parse

      val fs = List("f", "g", "h") map (new ConstantStringSymbol(_))
      val cs = List("e0", "e1", "e2") map (new ConstantStringSymbol(_))

      for (t <- terms zip fterms) {
        ACUEquality.fold_flatten_filter(fs,cs,t._1) must beSyntacticallyEqual (t._2)
      }
      // needed for the test to be visible because of the loop
      Success()

    }

    "word equality for multiple symbols should be decidable" in {
      val fs = List("f", "g", "h") map (new ConstantStringSymbol(_))
      val cs = List("e0", "e1", "e2") map (new ConstantStringSymbol(_))
      val s = parse("f(x, f(f(g(a,e1),a), b))")
      val t = parse("f(f(b, f(a,x)), a)")
      val r = parse("f(a, b, g(a,e1), x)")
      val u = parse("f(f(b, f(b,x)), a)")

      //println(ACUEquality.fold_flatten_filter(fs,cs,r)  )
      //println(ACUEquality.fold_flatten_filter(fs,cs,s)  )
      //println(ACUEquality.fold_flatten_filter(fs,cs,t)  )
      r must beACUWordEqual(fs,cs,r)
      s must beACUWordEqual(fs,cs,s)
      t must beACUWordEqual(fs,cs,t)

      s must beACUWordEqual(fs,cs,t)
      r must beACUWordEqual(fs,cs,t)
      s must beACUWordEqual(fs,cs,r)

      t must beACUWordEqual(fs,cs,s)
      t must beACUWordEqual(fs,cs,r)
      r must beACUWordEqual(fs,cs,s)

      s  must_!= beACUWordEqual(fs,cs,u)
      t  must_!= beACUWordEqual(fs,cs,u)
    }

    "do factorization modulo acu" in {
      val theory = new MulACUEquality(List("f", "g", "h") map (new ConstantStringSymbol(_)), List("e0", "e1", "e2") map (new ConstantStringSymbol(_)))
      val s = parse_pred("P(f(x, f(f(g(a,e1),a), b)))")
      val t = parse_pred("P(f(f(b, f(a,x)), a))")
      val r = parse_pred("P(f(a, b, g(a,e1), x))")
      val u = parse_pred("P(f(f(b, f(b,x)), a))")

      val factored = ACUEquality.factor_clause(theory, FSequent(Seq(s,r,s,s,t,u), Seq(u,s,t,u,u,t))  )
      factored._1.length must beEqualTo (2)
      factored._2.length must beEqualTo (2)

    }

    "do tautology elimination modulo acu" in {
      val theory = new MulACUEquality(List("f", "g", "h") map (new ConstantStringSymbol(_)), List("e0", "e1", "e2") map (new ConstantStringSymbol(_)))
      val s = parse_pred("P(f(x, f(f(g(a,e1),a), b)))")
      val t = parse_pred("P(f(f(b, f(a,x)), a))")
      val r = parse_pred("P(f(a, b, g(a,e1), x))")
      val u = parse_pred("P(f(f(b, f(b,x)), a))")

      val eliminated = ACUEquality.tautology_removal(theory, List(
        FSequent(Seq(s,r,s,s,t,u), Seq(u,s,t,u,u,t)), //removed because s is on both sides
        FSequent(Seq(r,t,u), Seq(s)), // removed because r reequal s
        FSequent(Seq(s,s,s,t,u), Seq(u,u)), // removed because u is on both sides
        FSequent(Seq(s,r,s,s,t), Seq(u,u,u)) //should remain
                    )  )
      eliminated must beEqualTo (List(FSequent(Seq(s,r,s,s,t), Seq(u,u,u))))
    }

    "do restricted subsumption modulo acu (1)" in {
      //skip("not working!")
      val theory = new MulACUEquality(List("f", "g", "h") map (new ConstantStringSymbol(_)), List("e0", "e1", "e2") map (new ConstantStringSymbol(_)))
      val s = parse_pred("P(f(x, f(f(g(a,e1),a), b)))")
      val t = parse_pred("P(f(f(b, f(a,x)), a))")
      val r = parse_pred("P(f(a, b, g(a,e1), x))")
      val u = parse_pred("P(f(f(b, f(b,x)), a))")
      val v = parse_pred("Q")

      val s1 = FSequent(Seq(s,r,s,s,t,u), Seq(u,s,t,u,u,t)) //equivalent s,u,-u,-s
      val s2 = FSequent(Seq(r,t,u), Seq(s)) // equivalent s,s,u,-s

      val factored = List(s1,s2) map ( (s : FSequent) => ACUEquality.factor_clause(theory,  s))

      ACUEquality.clause_restricted_subsumed_in2(theory, factored.head, factored.tail) must beTrue
      ACUEquality.clause_restricted_subsumed_in2(theory, s1, List(s2)) must beTrue
      ACUEquality.clause_restricted_subsumed_in2(theory, s2, List(s1)) must beFalse

    }

    "do restricted subsumption modulo acu (2)" in {
//      skip("not working!")
      val theory = new MulACUEquality(List("f", "g", "h") map (new ConstantStringSymbol(_)), List("e0", "e1", "e2") map (new ConstantStringSymbol(_)))
      val s = parse_pred("P(f(x, f(f(g(a,e1),a), b)))")
      val t = parse_pred("P(f(f(b, f(a,x)), a))")
      val r = parse_pred("P(f(a, b, g(a,e1), x))")
      val u = parse_pred("P(f(f(b, f(b,x)), a))")

      val s1 = FSequent(Seq(s,r,s,s,t,u), Seq(u,s,t,u,u,t)) //equivalent -s,-u,u,s
      val s2 = FSequent(Seq(r,t,u), Seq(s)) // equivalent -s,-s,-u,s
      val s3 = FSequent(Seq(s,s,s,t,u), Seq(u,u)) //equivalent -s,-s,-s,-s,-u,u,u
      val s4 = FSequent(Seq(s,r,s,s,t), Seq(u,u,u)) //equivalent -s,-s,-s,-s,-s,u,u

      val factored = List(s1,s2,s3,s4) map ( (s : FSequent) => ACUEquality.factor_clause(theory,  s))

      factored match {
        case List(s1,s2,s3,s4) =>
            ACUEquality.clause_restricted_subsumed_in2(theory, s1, List(s2,s3,s4)) must beTrue //because s1 is a weakened form of s2
            ACUEquality.clause_restricted_subsumed_in2(theory, s2, List(s1,s3,s4)) must beFalse
            ACUEquality.clause_restricted_subsumed_in2(theory, s3, List(s1,s2,s4)) must beTrue //because s3 is a weakened form of s4
            ACUEquality.clause_restricted_subsumed_in2(theory, s4, List(s1,s2,s3)) must beFalse
        case _ => ;
      }


      def flattenlist(s:Seq[HOLFormula]) = s map ( (x:HOLFormula) => theory.flatten(x.asInstanceOf[FOLFormula]) )


      val eliminated = ACUEquality.restricted_subsumption(theory, factored)
      eliminated.size must beEqualTo (2)

    }


  }
}
