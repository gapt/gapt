package at.logic.gui.prooftool.parser

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:42 PM
 */

import scala.swing.{Dialog, Label}
import java.io.{FileInputStream, InputStreamReader, IOException}
import java.util.zip.GZIPInputStream
import at.logic.parsing.language.xml.XMLParser.XMLProofDatabaseParser
import at.logic.parsing.readers.XMLReaders._
import at.logic.parsing.language.xml.ProofDatabase
import at.logic.parsing.calculi.xml.SimpleXMLProofParser
import at.logic.parsing.ParsingException
import at.logic.calculi.treeProofs.TreeProof
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.LKProof

class FileParser {

  def fileReader(f: String): Unit = {
    proofs = Nil
    proofdb = try {
      (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream(f)))) with XMLProofDatabaseParser).getProofDatabase()
    } catch {
      case e: IOException => // maybe input not gzipped, try again!
        (new XMLReader(new InputStreamReader(new FileInputStream(f))) with XMLProofDatabaseParser).getProofDatabase()
    }
  }

  def StabFileReader(f: String) = {
    proofdb = new ProofDatabase(Nil, Nil, Nil)
    proofs = (new XMLReader(new InputStreamReader(new FileInputStream(f))) with SimpleXMLProofParser).getNamedTrees()
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

  def addProofs(proofs : List[(String, LKProof)]) = {
    proofdb = new ProofDatabase(proofdb.proofs:::proofs, proofdb.axioms, proofdb.sequentLists)
  }

  def addSeqList(seqList : List[FSequent]) = {
    proofdb = new ProofDatabase(proofdb.proofs, proofdb.axioms,
      ("sequentList "+proofdb.sequentLists.size.toString, seqList)::proofdb.sequentLists)
  }

  def getSequentLists = proofdb.sequentLists
  def getProofs = proofdb.proofs:::proofs
  def getProofDB = proofdb

  private var proofdb = new ProofDatabase(Nil,Nil,Nil)
  private var proofs: List[(String, TreeProof[_])] = Nil
}
