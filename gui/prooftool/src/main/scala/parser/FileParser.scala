package at.logic.gui.prooftool.parser

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:42 PM
 */

import scala.swing.{Dialog, Label}
import java.io.{FileInputStream, InputStreamReader}
import at.logic.parsing.language.xml.XMLParser.XMLProofDatabaseParser
import at.logic.parsing.readers.XMLReaders._
import at.logic.parsing.language.xml.ProofDatabase

class FileParser {

  def fileReader(f: String): Unit = try {
    proofdb = (new XMLReader(new InputStreamReader(new FileInputStream(f))) with XMLProofDatabaseParser).getProofDatabase()
    proofNames = proofdb.proofs.map( x => x._1)
    clListNames = proofdb.sequentLists.map( x => x._1)
    ProofToolPublisher.publish(ProofDbChanged)
  } catch {
      case e: AnyRef =>
        val t = e.toString
        Dialog.showMessage(new Label(t),"Couldn't load file: "+f+"!\n\n"+t.replaceAll(",","\n"))
        ProofToolPublisher.publish(ProofDbChanged)
  }

  def getDB = proofdb
  def getProofNames = proofNames
  def getClListNames = clListNames

  private var proofdb =  new ProofDatabase(Nil,Nil,Nil)
  private var proofNames: List[String] = Nil
  private var clListNames: List[String] = Nil
}
