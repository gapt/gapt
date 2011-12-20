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
import io.Source
import at.logic.parsing.language.simple.SHLK

class FileParser {

  def xmlFileStreamReader(f: String) = new InputStreamReader(new FileInputStream(f), "UTF8")

  def gzFileStreamReader(f: String) = new InputStreamReader(new GZIPInputStream(new FileInputStream(f)), "UTF8")

  def ceresFileReader(input: InputStreamReader) = {
    proofs = Nil
    proofdb = (new XMLReader(input) with XMLProofDatabaseParser).getProofDatabase()
  }

  def stabFileReader(input: InputStreamReader) = {
    proofdb = new ProofDatabase(Nil, Nil, Nil)
    proofs = (new XMLReader(input) with SimpleXMLProofParser).getNamedTrees()
  }

  def lksFileReader(f: String) = {
    proofs = Nil
    proofdb = new ProofDatabase(SHLK.parseProofs(Source.fromFile(f).foldLeft("")((st, x) => st + x)), Nil, Nil)
  }

  def parseFile(path: String) = try {
    if (path.endsWith(".lks")) lksFileReader(path)
    else if (path.endsWith(".xml")) try {
      ceresFileReader(xmlFileStreamReader(path))
    } catch {
      case pe: ParsingException => stabFileReader(xmlFileStreamReader(path))
    }
    else if (path.endsWith(".gz")) try {
      ceresFileReader(gzFileStreamReader(path))
    } catch {
      case pe: ParsingException => stabFileReader(gzFileStreamReader(path))
    }
    else throw new Exception("Can not recognize file extension!")
    ProofToolPublisher.publish(ProofDbChanged)
  } catch {
    case e: AnyRef => errorMessage(e.toString, path)
  }

  def errorMessage(err: String, path: String) =
        Dialog.showMessage(new Label(err),"Could not load file: "+path+"!\n\n"+err.replaceAll(",",",\n").replaceAll(">",">\n"))

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
