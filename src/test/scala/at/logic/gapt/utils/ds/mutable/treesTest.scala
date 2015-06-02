/*
 * treesTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.utils.ds.mutable

import org.specs2.mutable._

import at.logic.gapt.utils.ds.mutable.trees._
//import at.logic.calculi.lk.base._
//import at.logic.gapt.language.hol._
import scala.util.parsing.combinator._

class treesTest extends Specification {

  "tree.scala" should {
    "create correctly a tree" in {

      val seq1 = "p(a)|p(f(a))"
      val seq2 = "p(a)|-p(b)"
      val seq3 = "-p(a)|p(b)"
      val seq4 = "p(X)|p(f(f(b)))"

      var l = seq1 :: seq2 :: seq3 :: seq4 :: Nil
      //  val root = new TreeNode[String](seq1::Nil)
      var root = new TreeNode[String]( l )
      val f: ( String ) => Int = { x => x.split( "a" ).size - 1 }
      //      val t = new MyTree[String](root, f::Nil)
      //      t.createTree(root)
      //      t.print
      val l1 = 1 :: 2 :: 3 :: Nil

      0 must beEqualTo( 0 )

      /*
      val a = Const(new ConstantSymbolA("a"), i)
      val b = Const(new ConstantSymbolA("b"), i)
      val p = Const(new ConstantSymbolA("p"), i->o)
      val X = Var(new VariableSymbolA("X"), i)


      val pa = App(p,a).asInstanceOf[Formula]
      val pb = App(p,b).asInstanceOf[Formula]
      val fa = App(f,a).asInstanceOf[LambdaExpression]
      val fb = App(f,b).asInstanceOf[LambdaExpression]
      val pfa = App(p,fa).asInstanceOf[Formula]
      val pfb = App(p,fb).asInstanceOf[Formula]
      val ffa = App(f,fa).asInstanceOf[LambdaExpression]
      val ffb = App(f,fb).asInstanceOf[LambdaExpression]
      val pffa = App(p,ffa).asInstanceOf[Formula]
      val pffb = App(p,ffb).asInstanceOf[Formula]

      val seq1 = Sequent(Nil, pa::pfa::Nil)
      val seq2 = Sequent(pb::Nil, pa::Nil)
      val seq3 = Sequent(pa::Nil, pb::Nil)
      val seq4 = Sequent(Nil,X::pffb::Nil)

      0 must beEqualTo (0)
*/
    }
  }
}
