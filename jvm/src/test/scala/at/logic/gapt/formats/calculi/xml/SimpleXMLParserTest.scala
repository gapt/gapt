/**
 * Description:
 */

package at.logic.gapt.formats.calculi.xml

import at.logic.gapt.formats.simple.SimpleXMLProofParser
import org.specs2.mutable._

import scala.xml._

import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base._

class SimpleXMLParserTest extends Specification {
  "parse correctly a simple tree" in {
    // use trivial string parser
    implicit val Parser: String => String = ( x => x )

    val ( name, tree ) = ( new NodeReader(
      <proof symbol="\pi" calculus="LKS">
        <rule type="or">
          <conclusion>\/_i=1..n P_i</conclusion>
          <rule type="axiom">
            <conclusion>\/_i=2..n P_i \/ P_1</conclusion>
          </rule>
        </rule>
      </proof>
    ) with SimpleXMLProofParser ).getNamedTree()( Parser )
    name must beEqualTo( "\\pi" )
    tree.vertex must beLike {
      case x: String if x == """\/_i=1..n P_i""" => ok
      case _                                     => ko
    }
  }

  "parse correctly a simple document" in {
    // use trivial string parser
    implicit val Parser: String => String = ( x => x )

    val trees = ( new NodeReader(
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
    ) with SimpleXMLProofParser ).getNamedTrees()( Parser )
    trees.size must beEqualTo( 1 )
    val ( name, tree ) = trees.head
    name must beEqualTo( "\\pi" )
    tree.vertex must beLike {
      case x: String if x == """\/_i=1..n P_i""" => ok
      case _                                     => ko
    }
  }
}
