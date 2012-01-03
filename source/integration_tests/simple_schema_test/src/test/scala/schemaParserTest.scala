
package at.logic.simple_schema_test

import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.transformations.ceres.unfolding.{applySchemaSubstitution, SchemaSubstitution1}
import org.specs._
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.writers.FileWriter
import org.specs.matcher.Matcher
import scala.xml.dtd._
import at.logic.transformations.ceres.projections.printSchemaProof

import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import scala.xml._
//import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.Sequent
import at.logic.transformations.ceres.struct._
import at.logic.language.schema.{IntVar, IntZero, IndexedPredicate, SchemaFormula, Succ, BigAnd, BigOr}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.slk._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.{Or => HOLOr, Neg => HOLNeg, And => HOLAnd, _}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.calculi.lksk.{Axiom => LKskAxiom,
WeakeningLeftRule => LKskWeakeningLeftRule,
WeakeningRightRule => LKskWeakeningRightRule,
ForallSkLeftRule, ForallSkRightRule, ExistsSkLeftRule, ExistsSkRightRule}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.definitionRules._
import scala.collection.immutable.Seq
import at.logic.transformations.ceres.projections._
import java.io.File.separator
import scala.io.Source
import java.io._
import at.logic.provers.prover9.Prover9
import at.logic.gui.prooftool.gui.Main
import at.logic.parsing.language.simple.SHLK


class schemaParserTest extends SpecificationWithJUnit {
    implicit val factory = defaultFormulaOccurrenceFactory
    import at.logic.language.schema._
    "schemaParserTest" should {
        "parse correctly a schema proof" in {
          val var3 = HOLVarFormula(new VariableStringSymbol("x3"))
                    val var4 = HOLVarFormula(new VariableStringSymbol("x4"))
                    val ax1  = at.logic.calculi.lk.propositionalRules.Axiom(var3::Nil, var3::Nil)
                    val ax2  = at.logic.calculi.lk.propositionalRules.Axiom(var4::Nil, var4::Nil)
                    val negl = NegLeftRule(ax1, var3)
                    val proof  = OrLeftRule(negl, ax2, var3, var4)

//          SHLK.parseProof( "1 = ax(x3: o |- x3: o)  " +
//                            "2 = negL( 1 , x3:o)" +
//                            "3 = ax(x4: o |- x4: o)" +
//                            "4 = orL(2, 3, x3:o, x4:o)", "4").toString must beEqual (proof.toString)

//          import at.logic.gui.prooftool.gui.Main
//          Main.display("Proof", proof) ; while(true){}

//          val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
//          val ax11 = at.logic.calculi.lk.propositionalRules.Axiom(A0::Nil, A0::Nil)
//          println("\n\n"+ax11.root.toString)

//          val p = SHLK.parseProof( "1 = ax(A(i+2) |- And A(0) BigAnd(i,0,s(i),A(i)))" +
//                                    "2 = negR(1,A(i+2))" +
//                                    "3 = ax(A(0) |- A(0))","3")

          println("\n\n\n---- SHLK Parser -----")
//          val p = SHLK.parseProof( "1 : ax(A(0) |- And A(0) BigAnd(i,0,s(i),A(i)))" +
//                                    "2 : negR(1,A(0))" +
//                                    "3 : ax(A(0) |- A(0))","2")
//          println("\n\n"+p.root.toString)

          import scala.io._
//          val s = Source.fromFile("/home/cvetan/gapt-trunk/source/integration_tests/simple_schema_test/src/test/resources/input1.lks").toList.foldLeft("")((ch,res) => ch + res)
          val s = Source.fromFile("target" + separator + "test-classes" + separator + "input1.lks").toList.foldLeft("")((ch,res) => ch + res)

          println("\n\ns = "+s)

//          val p = SHLK.parseProof(  "1 : pLink((psi,k)  A(0), BigAnd(i=0..k , (~A(i) \/ A(i+1) ) ) |- A(k+1))" +
//                                              "2 : ax(A(k+1) |- A(k+1))" +
//                                              "3 : negL(2, A(k+1))" +
//                                              "4 : ax(A(k+2) |- A(k+2))" +
//                                              "5 : orL(3, 4, ~A(k+1), A(k+2))" +
//                                              "6 : cut(1, 5, A(k+1))" +
//                                              "7 : andL(6, BigAnd(i=0..k , ( ~A(i) \/ A(i+1) ) ), (~A(k+1) \/ A(k+2) ) )", "7")

          val map = SHLK.parseProof(s)
//          val p = map.get("chi").get._2.get("root").get
          println("\n\npsi_b = "+  map.get("psi").get._1.get("root").get.root.toString()  )
          println("\n\npsi_s = "+  map.get("psi").get._2.get("root").get.root.toString()  )
          println("\n\nchi_b = "+  map.get("chi").get._1.get("root").get.root.toString()  )
          println("\n\nchi_s = "+  map.get("chi").get._2.get("root").get.root.toString()  )
          println("\n\nphi_b = "+  map.get("phi").get._1.get("root").get.root.toString()  )
          println("\n\nphi_s = "+  map.get("phi").get._2.get("root").get.root.toString()  )
//          Main.display("Proof", map.head._2._1) ; while(true){}

//          Main.display("psi", map.get("psi").get._1.get("root").get) ;

          println("map.size = "+map.size)
          map.foreach(pair => {
//            Main.display(pair._1, pair._2._1.get("root").get) ;
//            Main.display(pair._1, pair._2._2.get("root").get) ;//while(true){}
          })
          while(true){}
//          Main.display("Proof", p) ; while(true){}
//
//          val p = SHLK.parseProof(s,"root")
//          println("\n\np = "+  p.root.toString()  )
//          printSchemaProof(p)
//          Main.display("Proof", p) ; while(true){}

        }
    }
 }