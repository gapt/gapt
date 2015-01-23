
package at.logic.parsing.readers

import scala.xml.{Elem,Node}
import scala.xml.factory.XMLLoader
import at.logic.parsing.language.xml.XMLParser.XMLNodeParser
import javax.xml.parsers.{SAXParser, SAXParserFactory}

object XMLReaders {
  abstract class NodeReader(n: Node) extends XMLNodeParser {
    def getInput(): Node = n
  }

  abstract class XMLReader (r: java.io.InputStreamReader) extends XMLNodeParser {
    val reader = OfflineXMLWithoutCatalog.parser.getXMLReader()
    def getInput(): Node = scala.xml.Utility.trim (OfflineXMLWithoutCatalog.load(r))
  }

  //https://issues.scala-lang.org/browse/SI-2725
  //tweak not used because this workaround is now not compatible with last JDK and OpenJDK
  //see XMLParserTest for examples of offline XML validation with catalog
  object OfflineXMLWithoutCatalog extends XMLLoader[Elem] {
    override def parser: SAXParser = {
      val f = SAXParserFactory.newInstance()
      f.setNamespaceAware(false)
      f.setValidating(false)
      val result = f.newSAXParser()
      val reader = result.getXMLReader
      reader.setFeature("http://apache.org/xml/features/nonvalidating/load-external-dtd", false)
      result
    }
  }

}
