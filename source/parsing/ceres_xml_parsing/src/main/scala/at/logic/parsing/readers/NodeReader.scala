/** 
 * Description: 
 */

package at.logic.parsing.readers

import at.logic.parsing.InputParser
import scala.xml.{XML,Node}
import at.logic.parsing.language.xml.XMLParser.XMLNodeParser
import org.xml.sax.helpers.DefaultHandler
import org.xml.sax.InputSource
import javax.xml.parsers.SAXParserFactory
import org.xml.sax.ext.EntityResolver2

object XMLReaders {
  abstract class NodeReader(n: Node) extends XMLNodeParser {
    def getInput() : Node = n
  }

  abstract class XMLReader( r: java.io.Reader ) extends XMLNodeParser {
    def getInput() : Node = {
      //println("initializing reader")
      val f = SAXParserFactory.newInstance()
      f.setNamespaceAware(false)
      //println(f.getFeature("http://xml.org/sax/features/use-entity-resolver2"))

      val p = f.newSAXParser()

      p.getXMLReader.setEntityResolver(LogicAtHandler)

      XML.loadXML( new InputSource(r), p )
    }
  }

  object LogicAtHandler extends DefaultHandler with EntityResolver2  {
    override def  resolveEntity  (publicId: String, systemId : String) : InputSource = {
      //println("resolving entity:"+publicId+" "+systemId)
      try {
        super.resolveEntity(publicId, systemId)
      }
      catch {
        case e : Exception =>
        publicId match {
          case "http://www.logic.at/prooftool/xml/1.0/proof.dtd" =>
            val fr = new java.io.FileReader("dtd/proofdatabase-1.0.dtd")
            new InputSource(fr)
          case "http://www.logic.at/prooftool/xml/2.0/proof.dtd" =>
            val fr = new java.io.FileReader("dtd/proofdatabase-2.0.dtd")
            new InputSource(fr)
          case "http://www.logic.at/prooftool/xml/3.0/proof.dtd" =>
            val fr = new java.io.FileReader("dtd/proofdatabase-3.0.dtd")
            new InputSource(fr)
          case "http://www.logic.at/prooftool/xml/4.0/proof.dtd" =>
            val fr = new java.io.FileReader("dtd/proofdatabase-4.0.dtd")
            new InputSource(fr)
          case "http://www.logic.at/prooftool/xml/5.0/proof.dtd" =>
            val fr = new java.io.FileReader("dtd/proofdatabase-5.0.dtd")
            new InputSource(fr)
          case  _ => throw e
        }

        case _: Throwable => println("other error"); null
      }
    }

    def getExternalSubset(name: String, baseURI: String): InputSource = null

    def resolveEntity(name: String, publicId: String, baseURI: String, systemId: String): InputSource = resolveEntity(publicId, systemId)
  }

}
