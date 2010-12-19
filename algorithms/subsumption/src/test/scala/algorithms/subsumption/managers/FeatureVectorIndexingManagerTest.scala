/*
 * FeatureVectorIndexingManagerTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption.managers

import org.specs._
import org.specs.runner._

import at.logic.utils.ds.mutable.trees._
import at.logic.calculi.lk.base._
import at.logic.algorithms.subsumption._
//import at.logic.language.hol._

import at.logic.algorithms.matching.fol._

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.fol._



class gFeatureVectorIndexingManagerTest extends SpecificationWithJUnit {

  "tree.scala" should {
    "create correctly a tree" in {

      val seq1 = "p(a)|p(f(a))"
      val seq2 = "p(a)|-p(b)"
      val seq3 = "-p(a)|p(b)"
      val seq4 = "p(X)|p(f(f(b)))"
      //var l = seq1::seq2::seq3::seq4::Nil
     
      
//      val a = FOLConst(new ConstantStringSymbol("a"))
//      val b = HOLConst(new ConstantStringSymbol("b"), Ti())
//      val p = HOLConst(new ConstantStringSymbol("p"), Ti()->To())
//      val f = HOLConst(new ConstantStringSymbol("f"), Ti()->Ti())
//      val X = HOLVar(new VariableStringSymbol("X"), Ti())
//
//
//      val pa = App(p,a).asInstanceOf[HOLFormula]
//      val pb = App(p,b).asInstanceOf[HOLFormula]
//      val fa = App(f,a).asInstanceOf[HOLExpression]
//      val fb = App(f,b).asInstanceOf[HOLExpression]
//      val pfa = App(p,fa).asInstanceOf[HOLFormula]
//      val pfb = App(p,fb).asInstanceOf[HOLFormula]
//      val ffa = App(f,fa).asInstanceOf[HOLExpression]
//      val ffb = App(f,fb).asInstanceOf[HOLExpression]
//      val pffa = App(p,ffa).asInstanceOf[HOLFormula]
//      val pffb = App(p,ffb).asInstanceOf[HOLFormula]
//      val pX = App(p,X).asInstanceOf[HOLFormula]
//
//      val seq11 = Sequent(Nil, pa::pfa::Nil)
//      val seq21 = Sequent(pb::Nil, pa::Nil)
//      val seq31 = Sequent(pa::Nil, pb::Nil)
//      val seq41 = Sequent(Nil,pX::pffb::Nil)
//
//      val subsumedSeq = Sequent(Nil,pa::pX::Nil)


      val a = FOLConst(new ConstantStringSymbol("a"))
      val b = FOLConst(new ConstantStringSymbol("b"))
//      val p = HOLConst(new ConstantStringSymbol("p"), Ti()->To())
//      val f = HOLConst(new ConstantStringSymbol("f"), Ti()->Ti())
      val X = FOLVar(new VariableStringSymbol("x"))


      val pa = Atom(new ConstantStringSymbol("p"),a::Nil)
      val pb = Atom(new ConstantStringSymbol("p"),b::Nil)
      val fa = Function(new ConstantStringSymbol("f"),a::Nil)
      val fb = Function(new ConstantStringSymbol("f"),b::Nil)
      val pfa = Atom(new ConstantStringSymbol("p"),fa::Nil)
      val pfb = Atom(new ConstantStringSymbol("p"),fb::Nil)
      val ffa = Function(new ConstantStringSymbol("f"),fa::Nil)
      val ffb = Function(new ConstantStringSymbol("f"),fb::Nil)
      val pffa = Atom(new ConstantStringSymbol("p"),ffa::Nil)
      val pffb = Atom(new ConstantStringSymbol("p"),ffb::Nil)
      val pX = Atom(new ConstantStringSymbol("p"),X::Nil)

      val seq11 = Sequent(Nil, pa::pfa::Nil).asInstanceOf[SequentLike]
      val seq21 = Sequent(pb::Nil, pa::Nil).asInstanceOf[SequentLike]
      val seq31 = Sequent(pa::Nil, pb::Nil).asInstanceOf[SequentLike]
      val seq41 = Sequent(Nil,pX::pffb::Nil).asInstanceOf[SequentLike]

      val subsumedSeq = Sequent(Nil,pX::pa::Nil).asInstanceOf[SequentLike]


      var l = seq11::seq21::seq31::seq41::Nil
    //  val root = new TreeNode[String](seq1::Nil)
      var root = new TreeNode[SequentLike](l)
      val f1: (SequentLike) => Int = { x => x.getSequent.toStringSimple.split("p").size - 1}

      val t = new MyTree[SequentLike](root, f1::Nil)
      t.createTree(root)
      t.print
      val manager = new VectorTreeManager with StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm; var tree = t }
//      if(manager.forwardSubsumption1(t.root, f1::Nil, "abca"))
//          println("\n\n\nWORKS\n\n\n")

//      0 must beEqual (0)

//      if(manager.forwardSubsumption1(t.root, f1::Nil, "abca"))
      println("\n\n\n-----Forward subsumption-----\n\n\n")
      println("\n\nfeature vector subsumedSeq = "+f1(subsumedSeq))
      println("\nfeature vector subsumedSeq = "+subsumedSeq.getSequent.toStringSimple+"\n")

//      if(manager.subsumes(subsumedSeq, seq21))
//        println("\n\n\nSubsumed\n\n\n")
//      else
//        println("\n\n\nNOT subsumed\n\n\n")
      if(manager.forwardSubsumption1(t.root, f1::Nil, subsumedSeq))
          println("\n\n\nWORKS\n\n\n")
      else
          println("\n\n\nDoes NOT work\n\n\n")

      0 must beEqual (0)

    }
  }
}

