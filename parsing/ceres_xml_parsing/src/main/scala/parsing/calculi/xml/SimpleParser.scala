/**
 * Description: Parses the simple XML format agreed on with
 * Vincent Aravantinos: Trees with string-nodes.
 */

package at.logic.parsing.calculi.xml

import at.logic.utils.ds.trees._
import at.logic.parsing.language.xml.XMLParser.XMLNodeParser
import at.logic.parsing.ParsingException
import scala.xml.Utility.trim
import scala.xml._

trait SimpleXMLProofParser extends XMLNodeParser {

  def getNamedTrees[V]()(implicit parser: (String => V) ) : List[(String, Tree[V])] =
    getNamedTrees( getInput() )

  def getNamedTrees[V](n : Node )(implicit parser: (String => V) ) : List[(String, Tree[V])] =
    trim(n) match {
      case <prooftrees>{ns @ _* }</prooftrees> => {
        ns.toList.map( getNamedTree(_) )
      }
      case _ => throw new ParsingException("Could not parse XML: " + n.toString)
    }

  def getNamedTree[V]()(implicit parser: (String => V) ) : (String, Tree[V]) = getNamedTree( getInput() )

  def getNamedTree[V]( n : Node )(implicit parser: (String => V) ) : (String, Tree[V]) = 
    (n.attribute("symbol").get.head.text, getTree( n ) )

  def getTree[V]( n : Node )(implicit parser: (String => V) ) : Tree[V] = getTreeRec( n )

  private def getTreeRec[V]( n : Node )(implicit parser: (String => V) ) : Tree[V] =
      trim(n) match {
        case <proof>{ ns @ _* }</proof> => {
          // TODO: read calculus
          getTreeRec( ns.head )
        }
        case <rule><conclusion>{ c @ _ }</conclusion>{ ns @ _* }</rule> => {
          val prems = ns.filter( n => n.label == "rule" ).map( n => getTreeRec( n ) ).toList
          val conc = parser(c.head.text)
          if ( prems.size == 0 )
            new LeafTree[V]( conc )
          else if ( prems.size == 1 )
            new UnaryTree[V]( conc, prems.head )
          else if ( prems.size == 2 )
            new BinaryTree[V]( conc, prems.head, prems.tail.head )
          else
            throw new ParsingException( "Do not support " + prems.size + "-ary trees!" )
        }
        case <prooflink/> => {
          //n.attribute("symbol").get.head.text
          // TODO: create DAG!?
          throw new ParsingException("Could not parse prooflink node (not supported yet): " + n.toString)
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
}
