package at.logic.algorithms.hlk

import at.logic.utils.testing.ClasspathFileCopier
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.execute.Success
import at.logic.parsing.language.hlk.{HOLASTParser, HLKHOLParser, ast}
import at.logic.parsing.language.hlk.ast.LambdaAST
import java.io.File.separator
import at.logic.language.lambda.types.{To, Ti, TA}
import at.logic.language.hol._
import at.logic.calculi.lk.base.FSequent
import at.logic.language.lambda.types.Ti
import at.logic.language.lambda.types.To
import at.logic.language.lambda.App


/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 10/14/13
 * Time: 3:02 PM
 * To change this template use File | Settings | File Templates.
 */
@RunWith(classOf[JUnitRunner])
class HybridLatexParserTest extends SpecificationWithJUnit with ClasspathFileCopier {
  val p1 =
    """\AX{T,MON(h_1,\alpha)}{MON(h_1,\alpha) }
      |\AX{ NOCC(h_1,\alpha,\sigma)}{NOCC(h_1,\alpha,\sigma)}
      |\EXR{}{ NOCC(h_1,\alpha,\sigma)}{(exists s NOCC(h_1,\alpha,s))}
      |\ANDR{T,MON(h_1,\alpha), NOCC(h_1,\alpha,\sigma)}{MON(h_1,\alpha) & (exists s NOCC(h_1,\alpha,s))}
      |\EXR{}{T,MON(h_1,\alpha), NOCC(h_1,\alpha,\sigma)}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\ANDL{T, MON(h_1,\sigma) & NOCC(h_1,\sigma,x)}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\EXL{}{T, (exists h (MON(h,\sigma) & NOCC(h,\sigma,x)))}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\ALLL{}{T, (all n exists h (MON(h,n) & NOCC(h,n,x)))}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\DEF{T,A(\sigma)}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\ALLR{}{T,A(\sigma)}{(all n exists h (MON(h,n) & (exists s NOCC(h,n,s))))}
      |\DEF{T,A(\sigma)}{C}
      |\CONTINUEWITH{\rho(\sigma)}
      |""".stripMargin

  def checkformula(f:String) = {
    HybridLatexParser.parseAll(HybridLatexParser.formula,f) match {
      case HybridLatexParser.Success(r,_) =>
        ok(r.toString)
      case HybridLatexParser.NoSuccess(msg, input) =>
        ko("Error at "+input.pos+": "+msg)
    }
  }


  "Hybrid Latex-GAPT" should {
    "correctly handle latex macros in formulas (1)" in {
      checkformula("\\benc{j_1<n+1}")
      ok
    }

    "correctly handle latex macros in formulas (2)" in {
      checkformula("\\ite{\\benc{j_1<n+1}}{h'(j_1)}{\\alpha}")
      ok
    }

    "correctly handle latex macros in formulas (3)" in {
      checkformula("\\ite{\\ienc{j_1<n+1}}{h'(j_1)}{\\alpha}")
      ok
    }

    "correctly handle latex macros in formulas (4)" in {
      checkformula("\\ite{\\benc{j_1<n+1}}{h'(j_1)}{\\alpha} = 0")
      ok
    }

    "accept the proof outline" in {
      //println(p1)
      HybridLatexParser.parseAll(HybridLatexParser.rules, p1) match {
        case HybridLatexParser.Success(r : List[Token] , _) =>
          //println(r)
          val lterms : List[LambdaAST] = r.flatMap(_ match {
            case RToken(_,_,a, s,_) => a++s
            case TToken(_,_,_) => Nil
            case AToken(_,_,a,s) => a++s
          })


          //println(lterms.flatMap(_.varnames).toSet)

          ok("successfully parsed "+r)
        case HybridLatexParser.NoSuccess(msg, input) =>
          ko("parsing error at "+input.pos +": "+msg)
      }
      ok
    }

    "accept the proof outline with the parse interface" in {
        val r = HybridLatexParser.parse(p1)
        ok
    }

    "correctly infer replacement terms in equalities" in {
      import at.logic.calculi.lk.EquationVerifier.{Equal, Different, EqualModuloEquality, checkReplacement}
      val List(a) = List("a") map (x => HOLConst(x, Ti))
      val List(f,g) = List("f","g") map (x => HOLConst(x, Ti -> Ti))
      val List(p) = List("p") map (x => HOLConst(x, Ti -> (Ti -> (Ti -> To)) ))
      val t1 = App(p, List(App(f,a), App(f,App(g,App(f,a))), a  ))
      val t2 = App(p, List(App(f,a), App(f,App(g,App(g,a))), a  ))
      val fa = App(f,a)
      val ga = App(g,a)

      checkReplacement(fa,ga,t1,t2) match {
        case Equal => ko("Terms "+t1+" and "+t2+" considered as equal, but they differ!")
        case Different => ko("Terms "+t1+" and t2 considered as (completely) different, but they differ only modulo one replacement!")
        case EqualModuloEquality(path) =>
          //println("Path:"+path)
          ok
      }

      checkReplacement(fa,ga,t1,t1) match {
        case Equal => ok
        case Different => ko("Terms "+t1+" and t2 considered as (completely) different, but they are equal!")
        case EqualModuloEquality(path) => ko("Found an equality modulo "+Equation(fa.asInstanceOf[HOLExpression],ga.asInstanceOf[HOLExpression])+" but should be equal!")
      }
      ok
    }


    "load the simple example from file and parse it" in {
        val r = HybridLatexParser.parseFile(tempCopyOfClasspathFile("simple.llk"))
        val p = HybridLatexParser.createLKProof(r)
        //println(p)

        ok
    }


    "load the commutativity of + proof from file and parse it" in {
        val r = HybridLatexParser.parseFile(tempCopyOfClasspathFile("komm.llk"))
        val p = HybridLatexParser.createLKProof(r)
        (p.proof("THEPROOF")) must not throwAn() //exception

        ok
    }

    "load the 3-2 pigeon hole example from file and parse it" in {
        val r = HybridLatexParser.parseFile(tempCopyOfClasspathFile("pigeon32.llk"))
        val p = HybridLatexParser.createLKProof(r)
        (p.proof("PROOF")) must not throwAn() //exception

        ok
    }

    "load the tape3 proof from file" in {
        val r = HybridLatexParser.parseFile(tempCopyOfClasspathFile("tape3.llk"))
        val p = HybridLatexParser.createLKProof(r)
        p.proofs.length must be_>(0)
        p.Definitions.toList.length must be_>(0)
        p.axioms.length must be_>(0)
        ok
    }


  }

  "Tactics" should {
    "correctly prove the instance of an axiom" in {
      val vmap = Map[String,TA]( "x" -> Ti, "y" -> Ti, "z" -> Ti)
      val cmap = Map[String,TA]( "a" -> Ti, "1" -> Ti, "+" -> (Ti->(Ti->Ti)))
      val naming : String => HOLExpression = x => { if (vmap contains x) HOLVar(x,vmap(x)) else
                                                                       HOLConst(x,cmap(x)) }
      val axiom =  HLKHOLParser.ASTtoHOL( naming, HybridLatexParser.parseFormula("(all x all y all z (x+(y+z)=(x+y)+z))"))
      val instance = HLKHOLParser.ASTtoHOL( naming, HybridLatexParser.parseFormula("a+((1+x)+y)=(a+(1+x))+y"))
      val t1 = Function(HOLConst("+",Ti -> (Ti -> Ti)),List(
                          HOLConst("1", Ti),
                          HOLVar("x",Ti)))
      val t2 = HOLConst("a", Ti)
      val x = HOLVar("x",Ti)
      val y = HOLVar("y",Ti)
      val z = HOLVar("z",Ti)
      val sub = Substitution( List((x,t2), (y,t1), (z,y)) )
      val p = HybridLatexParser.proveInstance(axiom.asInstanceOf[HOLFormula],instance.asInstanceOf[HOLFormula], sub)
      p.root.occurrences must haveSize(2)
      p.root.antecedent must haveSize(1)
      p.root.succedent must haveSize(1)
      p.root.antecedent(0).formula mustEqual(axiom)
      p.root.succedent(0).formula mustEqual(instance)
    }
  }
}
