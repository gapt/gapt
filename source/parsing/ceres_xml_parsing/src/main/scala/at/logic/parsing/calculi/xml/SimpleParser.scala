/**
 * Description: Parses the simple XML format agreed on with
 * Vincent Aravantinos: Trees with string-nodes.
 */

package at.logic.parsing.calculi.xml

import at.logic.calculi.proofs.{NullaryRuleTypeA, UnaryRuleTypeA, BinaryRuleTypeA}
import at.logic.calculi.proofs._
import at.logic.utils.ds.trees.{LeafTree, UnaryTree, BinaryTree}
import at.logic.parsing.language.xml.XMLParser.XMLNodeParser
import at.logic.parsing.ParsingException
import scala.xml.Utility.trim
import scala.xml._

// These objects are needed for stab. (may be moved to other file?)
case object NullaryRuleType extends NullaryRuleTypeA
case object UnaryRuleType extends UnaryRuleTypeA
case object BinaryRuleType extends BinaryRuleTypeA

trait SimpleXMLProofParser extends XMLNodeParser {

  def getNamedTrees[V]()(implicit parser: (String => V) ) : List[(String, TreeProof[V])] =
    getNamedTrees( getInput() )

  def getNamedTrees[V](n : Node )(implicit parser: (String => V) ) : List[(String, TreeProof[V])] =
    trim(n) match {
      case <prooftrees>{ns @ _* }</prooftrees> => {
        ns.toList.map( getNamedTree(_)(parser: (String => V)) )
      }
      case _ => throw new ParsingException("Could not parse XML: " + n.toString)
    }

  def getNamedTree[V]()(implicit parser: (String => V) ) : (String, TreeProof[V]) = getNamedTree( getInput() )

  def getNamedTree[V]( n : Node )(implicit parser: (String => V) ) : (String, TreeProof[V]) =
    (n.attribute("symbol").get.head.text, getTree( n ) )

  def getTree[V]( n : Node )(implicit parser: (String => V) ) : TreeProof[V] = getTreeRec( n )

  private def getTreeRec[V]( n : Node )(implicit parser: (String => V) ) : TreeProof[V] =
      trim(n) match {
        case <proof>{ ns @ _* }</proof> => {
          // TODO: read calculus
          getTreeRec( ns.head )
        }
        case <rule><conclusion>{ c @ _ }</conclusion>{ ns @ _* }</rule> => {
 //         val prems = ns.filter( n => n.label == "rule" ).map( n => getTreeRec( n ) ).toList
          val prems = ns.map( getTreeRec(_)(parser: (String => V)) ).toList
          val conc = parser(c.head.text)
          if ( prems.size == 0 )
            new LeafTree[V]( conc ) with NullaryTreeProof[V] {
              def rule = NullaryRuleType
            }
          else if ( prems.size == 1 )
            new UnaryTree[V]( conc, prems.head ) with UnaryTreeProof[V] {
              def rule = UnaryRuleType
              override def name = (n \ "@type").text
            }
          else if ( prems.size == 2 )
            new BinaryTree[V]( conc, prems.head, prems.tail.head ) with BinaryTreeProof[V] {
              def rule = BinaryRuleType
              override def name = (n \ "@type").text
            }
          else
            throw new ParsingException( "Do not support " + prems.size + "-ary trees!" )
        }
        case <prooflink /> => {
          //Simple implementation of prooflink, should be changed later!
          val conc = parser((n \ "@symbol").text)
          new LeafTree[V]( conc ) with NullaryTreeProof[V] {
            def rule = NullaryRuleType
          }
          //n.attribute("symbol").get.head.text
          // TODO: create DAG!?
          //throw new ParsingException("Could not parse prooflink node (not supported yet): " + n.toString)
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
}
