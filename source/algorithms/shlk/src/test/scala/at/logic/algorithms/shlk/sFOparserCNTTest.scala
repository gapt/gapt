/*
* sQMONparserTest.scala
*
* To change this template, choose Tools | Template Manager
* and open the template in the editor.
*/

package at.logic.algorithms.shlk

import at.logic.language.schema._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, NegLeftRule, Axiom}
import at.logic.calculi.lksk.Axiom
import at.logic.parsing.readers.StringReader
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.parsing.readers.StringReader
import scala.io._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success
import at.logic.algorithms.lk.{getCutAncestors, getAncestors}
import at.logic.calculi.slk.{TermEquivalenceRule1, TermRightEquivalenceRule1}
import at.logic.calculi.occurrences.FormulaOccurrence


@RunWith(classOf[JUnitRunner])
class sFOparserCNTTest extends SpecificationWithJUnit {
  private class MyParser extends StringReader("")
  "sFOparserCNT" should {

    sequential
    "parse correctly David's proof " in {
      skipped("has eigenvariable condition errors")

      //          sFOParser.parseProof( "1 : ax(x3: o |- x3: o)  " +
      //                            "2 : negL( 1 , x3:o)" +
      //                            "3 : ax(x4: o |- x4: o)" +
      //                            "4 : orL(2, 3, x3:o, x4:o)", "4").toString must beEqualTo (proof.toString)

      val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
      val i = IntVar(new VariableStringSymbol("i"))
      val k = IntVar(new VariableStringSymbol("k"))
      val Ai2 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(Succ(i)))
      val Ai = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
      val f1 = at.logic.language.schema.And(A0, BigAnd(i,Ai,IntZero(),Succ(i)))
      val ax11 = at.logic.calculi.lk.propositionalRules.Axiom(A0::Nil, A0::Nil)
      //          println("\n\n"+ax11.root.toString)

      //          sFOParser.parseProof( "1 : ax(A(i+2) |- And A(0) BigAnd(i,0,s(i),A(i)))" +
      //                           "2 : negR(1,A(i+2))","2").root.toString

      //          sFOParser.parseProof( "1 : pLink((psi,k+1) , A(0) |- A(0))","1").root.toString
      //          println("\n\n")



      //          val p = sFOParser.parseProof(  "1 : pLink((psi,k)  A(0), BigAnd(i=0..k , (~A(i) \\/ A(i+1) ) ) |- A(k+1))" +
      //                                    "2 : ax(A(k+1) |- A(k+1))" +
      //                                    "3 : negL(2, A(k+1))" +
      //                                    "4 : ax(A(k+2) |- A(k+2))" +
      //                                    "5 : orL(3, 4, ~A(k+1), A(k+2))" +
      //                                    "6 : cut(1, 5, A(k+1))" +
      //                                    "root : andL(6, BigAnd(i=0..k , ( ~A(i) \\/ A(i+1) ) ), (~A(k+1) \\/ A(k+2) ) )", "root")
      //          println("\n\np = "+  p.root.toString())
      //          p.root.toString must beEqualTo ("(i.((¬(A(i)) ∨ A(s(i)))) ⋀ 0)(s(k)), A(0) :- A(s(s(k)))")
      //          val s = Source.fromFile("/home/cvetan/gapt-trunk/source/integration_tests/simple_schema_test/src/test/resources/input1.lks").toList.foldLeft("")((ch,res) => ch + res)
      //          val s = Source.fromFile("target" + separator + "test-classes" + separator + "input_multi_indxs.lks").toList.foldLeft("")((ch,res) => ch + res)
      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "David.lks"))

      //      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sEXP.lks"))
      //      val map1 = sFOParser.parseProof(s1)


      val map = sFOParserCNT.parseProof(s)
      //          println("\n\np = "+  map.get("chi").get._1.get("root").get.root.toString()  )
      //                       val p = map.get("chi").get._2.get("root").get
      //          println("\n\npsi_b = "+  map.get("psi").get._1.get("root").get.root.toString()  )
      //          println("\n\npsi_s = "+  map.get("psi").get._2.get("root").get.root.toString()  )
      //          println("\n\nchi_b = "+  map.get("chi").get._1.get("root").get.root.toString()  )
      //          println("\n\nchi_s = "+  map.get("chi").get._2.get("root").get.root.toString()  )
      //          println("\n\nphi_b = "+  map.get("phi").get._1.get("root").get.root.toString()  )
      //          println("\n\nphi_s = "+  map.get("phi").get._2.get("root").get.root.toString()  )
      //          Main.display("Proof", map.head._2._1) ; while(true){}

      //          Main.display("phi", map.get("phi").get._2.get("root").get) ;


      //          val seq = sFOParser.parseSequent("P(n,f(0,x)) |- ")
      //          val seq = sFOParser.parseSequent("Forall x P(f(k,x)), P(x(k)) |- ")
      //          println(seq)

      //      println("\n\n"+map.get("\\sigma").get._2.get("root").get.root)
      //println(Console.BLUE+"\n---- Print David's Proof ----\n"+Console.RESET)
//      val p = map.get("\\varphi").get._2.get("root").get
      val p1 = map.get("\\mu").get._2.get("root").get
      val p2 = map.get("\\rho").get._2.get("root").get
      val p3 = map.get("\\zeta").get._2.get("root").get
      val p4 = map.get("\\omega").get._2.get("root").get
      val p5 = map.get("\\xi").get._2.get("root").get
      val p6 = map.get("\\varphi").get._2.get("root").get

      val cc2:FormulaOccurrence = p2.root.antecedent.tail.tail.head
      val cc_zeta_1:FormulaOccurrence = p3.root.succedent.head
      val cc_zeta_2:FormulaOccurrence = p3.root.antecedent.tail.tail.head
      val cc4:FormulaOccurrence = p4.root.succedent.head
      val cc_xi_1:FormulaOccurrence = p5.root.antecedent.last
      val cc_xi_2:FormulaOccurrence = p5.root.succedent.head
      val cc_xi_3:FormulaOccurrence = p5.root.antecedent.tail.head
      val cc6 = p6.root.antecedent.tail.head :: p6.root.antecedent.last ::Nil
      FixedFOccs.foccs = cc2::cc_xi_1::cc_xi_2::cc_xi_3::cc_zeta_1::cc_zeta_2::cc4::Nil  :::cc6
      println("\nfocc.formula = "+FixedFOccs.foccs)

      //      val rcc = RelevantCC("\\varphi")._1.flatten
      //      println("\n\nstruct = "+struct)
      //      val cs = StandardClauseSet.transformStructToClauseSet( struct )

      //      println("\nvarphi = "+varphi.root)


      // specs2 require a least one Result, see org.specs2.specification.Example
      Success()

    }
  }
}


