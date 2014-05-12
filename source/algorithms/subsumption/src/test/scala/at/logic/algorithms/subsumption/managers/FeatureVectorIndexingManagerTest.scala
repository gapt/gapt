/*
 * FeatureVectorIndexingManagerTest.scala
 *
 */

/* 
package at.logic.algorithms.subsumption.managers

import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

import at.logic.utils.ds.mutable.trees._
import at.logic.calculi.lk.base.FSequent
import at.logic.algorithms.subsumption._
import at.logic.language.fol._

@RunWith(classOf[JUnitRunner])
class FeatureVectorIndexingManagerTest extends SpecificationWithJUnit {

  "tree.scala" should {
    "create correctly a tree" in {

      val a = FOLConst("a")
      val b = FOLConst("b")
      val X = FOLVar("x")

      val pa = Atom("p",a::Nil)
      val pb = Atom("p",b::Nil)
      val fa = Function("f",a::Nil)
      val fb = Function("f",b::Nil)
      val pfa = Atom("p",fa::Nil)
      val pfb = Atom("p",fb::Nil)
      val ffa = Function("f",fa::Nil)
      val ffb = Function("f",fb::Nil)
      val pffa = Atom("p",ffa::Nil)
      val pffb = Atom("p",ffb::Nil)
      val pX = Atom("p",X::Nil)
  
      val seq11 = FSequent(Nil, pa::pfa::Nil)
      val seq21 = FSequent(pb::Nil, pa::Nil)
      val seq31 = FSequent(pa::Nil, pb::Nil)
      val seq41 = FSequent(Nil, pX::pffb::Nil)

      val subsumedSeq = new FSequent(Nil, pX::pa::Nil)

      val l = seq11::seq21::seq31::seq41::Nil

      def termDepth(exp: FOLExpression): Int = exp match {
        case FOLVar(_) => 0
        case FOLConst(_) => 0
        case Atom(_,args) => args.map(x => termDepth(x)).foldLeft(0)((x,y) => 1+math.max(x, y))
        case Function(_,args) => args.map(x => termDepth(x)).foldLeft(0)((x,y) => 1+math.max(x, y))
      }

      def depth: (FSequent) => Int = {
        seq => {
          val a = seq._1.map(x =>  termDepth(x.asInstanceOf[FOLExpression])).foldLeft(0)((x,y) => math.max(x, y))
          val b = seq._2.map(x =>  termDepth(x.asInstanceOf[FOLExpression])).foldLeft(0)((x,y) => math.max(x, y))
          math.max(a,b)
        }
      }

      var root = new TreeNode[FSequent](l)
      val featureList = depth::Nil
      var subsumpMNGR = new VectorTreeManager with StillmanSubsumptionAlgorithm[LambdaExpression] {
        var seqList = l;
        var tree = new Trie(l, featureList);
        tree.createTree
        var features = featureList;
        def forwardSubsumption = forwardSubsumptionRec(tree.root, features, subsumedSeq)
        val matchAlg = FOLMatchingAlgorithm
      }
      subsumpMNGR.forwardSubsumption

      0 must beEqualTo (0)

    }
  }
}
*/

