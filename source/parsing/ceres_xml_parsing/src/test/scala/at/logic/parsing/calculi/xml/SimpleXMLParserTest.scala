/** 
 * Description: 
**/

package at.logic.parsing.calculi.xml

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import scala.xml._

import at.logic.parsing.readers.XMLReaders._
import at.logic.language.hol._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._

@RunWith(classOf[JUnitRunner])
class SimpleXMLParserTest extends SpecificationWithJUnit {
    "parse correctly a simple tree" in {
      // use trivial string parser
      implicit val Parser : String => String = (x => x)

      val (name, tree) = (new NodeReader(
        <proof symbol="\pi" calculus="LKS">
          <rule type="or">
            <conclusion>\/_i=1..n P_i</conclusion>
            <rule type="axiom">
              <conclusion>\/_i=2..n P_i \/ P_1</conclusion>
            </rule>
          </rule>
        </proof>
      ) with SimpleXMLProofParser).getNamedTree()(Parser)
      name must beEqualTo("\\pi")
      tree.vertex must beLike{ case x : String if x == """\/_i=1..n P_i""" => ok
                               case _ => ko }
    }

    "parse correctly a simple document" in {
      // use trivial string parser
      implicit val Parser : String => String = (x => x)

      val trees = (new NodeReader(
        <prooftrees>
          <proof symbol="\pi" calculus="LKS">
            <rule type="or">
              <conclusion>\/_i=1..n P_i</conclusion>
              <rule type="axiom">
                <conclusion>\/_i=2..n P_i \/ P_1</conclusion>
              </rule>
            </rule>
          </proof>
        </prooftrees>
      ) with SimpleXMLProofParser).getNamedTrees()(Parser)
      trees.size must beEqualTo(1)
      val (name, tree) = trees.head
      name must beEqualTo("\\pi")
      tree.vertex must beLike{ case x : String if x == """\/_i=1..n P_i""" => ok
                               case _ => ko }
    }
}
