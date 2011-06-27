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
import at.logic.parsing.calculi.xml.SimpleXMLProofParser
import at.logic.parsing.ParsingException
import at.logic.calculi.treeProofs.TreeProof

class FileParser {

  def fileReader(f: String): Unit = {
    proofdb = (new XMLReader(new InputStreamReader(new FileInputStream(f))) with XMLProofDatabaseParser).getProofDatabase()
    proofs = proofdb.proofs
    proofNames = proofdb.proofs.map( x => x._1)
    sequentListNames = proofdb.sequentLists.map( x => x._1)
  }

  def StabFileReader(f: String) = {
    proofs = (new XMLReader(new InputStreamReader(new FileInputStream(f))) with SimpleXMLProofParser).getNamedTrees()
    proofNames = proofs.map( x => x._1)
    sequentListNames = Nil
  }

  def parseFile(path: String) = try {
    fileReader(path)
    ProofToolPublisher.publish(ProofDbChanged)
  } catch {
    case pe: ParsingException => try {
      StabFileReader(path)
      ProofToolPublisher.publish(ProofDbChanged)
    } catch {
      case e: AnyRef => errorMessage(pe.toString + "\n\n" + e.toString, path)
    }
    case e: AnyRef => errorMessage(e.toString, path)
  }

  def errorMessage(err: String, path: String) =
        Dialog.showMessage(new Label(err),"Couldn't load file: "+path+"!\n\n"+err.replaceAll(",","\n").replaceAll(">",">\n"))

  def getSequentLists = proofdb.sequentLists
  def getSequentListNames = sequentListNames
  def getProofs = proofs
  def getProofNames = proofNames

  private var proofdb = new ProofDatabase(Nil,Nil,Nil)
  private var proofs: List[(String, TreeProof[_])] = Nil
  private var proofNames: List[String] = Nil
  private var sequentListNames: List[String] = Nil
}
