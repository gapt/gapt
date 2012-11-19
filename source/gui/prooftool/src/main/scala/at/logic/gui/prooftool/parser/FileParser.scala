package at.logic.gui.prooftool.parser

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:42 PM
 */

import scala.swing.Dialog
import java.io.{FileInputStream, InputStreamReader}
import java.util.zip.GZIPInputStream
import at.logic.parsing.language.xml.XMLParser.XMLProofDatabaseParser
import at.logic.parsing.readers.XMLReaders._
import at.logic.parsing.language.xml.ProofDatabase
import at.logic.parsing.calculi.xml.SimpleXMLProofParser
import at.logic.parsing.ParsingException
import at.logic.calculi.treeProofs.TreeProof
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.LKProof
import at.logic.algorithms.shlk.ParseQMON
import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.utils.ds.trees.Tree
import at.logic.language.hol.HOLExpression
import at.logic.gui.prooftool.gui.Main
import at.logic.provers.prover9.ivy.IvyParser
import at.logic.provers.prover9.ivy.conversion.IvyToRobinson
import at.logic.language.schema.dbTRS
import at.logic.transformations.ceres.clauseSchema.ParseResSchema

class FileParser {

  def fileStreamReader(f: String) = new InputStreamReader(new FileInputStream(f), "UTF8")

  def gzFileStreamReader(f: String) = new InputStreamReader(new GZIPInputStream(new FileInputStream(f)), "UTF8")

  def ceresFileReader(input: InputStreamReader) {
    proofs = Nil
    termTrees = Nil
    proofdb = (new XMLReader(input) with XMLProofDatabaseParser).getProofDatabase()
  }

  def stabFileReader(input: InputStreamReader) {
    termTrees = Nil
    proofdb = new ProofDatabase(Map(), Nil, Nil, Nil)
    proofs = (new XMLReader(input) with SimpleXMLProofParser).getNamedTrees()
  }

  def lksFileReader(input: InputStreamReader) {
    proofs = Nil
    termTrees = Nil
    val defs = Map.empty[HOLExpression,HOLExpression] //TODO: change this line to get defs from dbTRS.
    //  val start = System.currentTimeMillis()
    proofdb = new ProofDatabase(defs, ParseQMON.parseProofs(input), Nil, Nil)
    //  val end = System.currentTimeMillis()
    //  println("parsing took " + (end - start).toString)
  }

  def rsFileReader(input: InputStreamReader) {
    ParseResSchema(input)
    val rs = Nil  //TODO: change this line to get resolution terms as TreeProofs from ResolutionProofSchema.
    proofs = proofs:::rs
    val defs = Map.empty[HOLExpression,HOLExpression] //TODO: change this line to get defs from dbTRS.
    addDefinitions(defs)
  }

  def ivyFileReader(path: String) {
    val ivy = IvyToRobinson(IvyParser.apply(path, IvyParser.IvyStyleVariables))
    proofs = Nil
    termTrees = Nil
    proofdb = new ProofDatabase(Map(), ("ivy_proof", RobinsonToLK(ivy))::Nil, Nil, Nil)
  }

  def parseFile(path: String) { try {
    if (path.endsWith(".lks")) lksFileReader(fileStreamReader(path))
    else if (path.endsWith(".lks.gz")) lksFileReader(gzFileStreamReader(path))
    else if (path.endsWith(".rs")) rsFileReader(fileStreamReader(path))
    else if (path.endsWith(".rs.gz")) rsFileReader(gzFileStreamReader(path))
    else if (path.endsWith(".xml")) try {
      ceresFileReader(fileStreamReader(path))
    } catch {
      case pe: ParsingException =>
        Main.questionMessage("There was a parsing exception:\n\n \t " + pe.getMessage + "\n\nContinue with another parser?") match {
          case Dialog.Result.Yes => stabFileReader(fileStreamReader(path))
          case _ =>
        }
    }
    else if (path.endsWith(".xml.gz")) try {
      ceresFileReader(gzFileStreamReader(path))
    } catch {
      case pe: ParsingException =>
        Main.questionMessage("There was a parsing exception:\n\n \t " + pe.getMessage + "\n\nContinue with another parser?") match {
          case Dialog.Result.Yes => stabFileReader(gzFileStreamReader(path))
          case _ =>
        }
    }
    else if (path.endsWith(".ivy")) ivyFileReader(path)
  //  else if (path.endsWith(".ivy.gz")) ivyFileReader(path) // This will be added later
    else throw new Exception("Can not recognize file extension!")
    ProofToolPublisher.publish(ProofDbChanged)
  } catch {
      case err: Throwable =>
        Main.errorMessage("Could not load file: " + path + "!\n\n" + Main.getExceptionString(err))
  }}

  def addProofs(proofs: List[(String, LKProof)]) {
    proofdb = new ProofDatabase(proofdb.Definitions, proofdb.proofs ::: proofs, proofdb.axioms, proofdb.sequentLists)
  }

  def addSeqList(seqList: List[FSequent]) {
    addSeqList("sequentList ", seqList)
  }

  def addSeqList(name: String, seqList: List[FSequent]) {
    proofdb = new ProofDatabase(proofdb.Definitions, proofdb.proofs, proofdb.axioms,
      (name + proofdb.sequentLists.size.toString, seqList) :: proofdb.sequentLists)
  }

  def addTermTree(struct: Tree[_]) {
    termTrees = ("struct " + termTrees.size.toString, TermType.Unknown, struct) :: termTrees
  }

  def addTermTree(name: String, term: Tree[_]) {
    termTrees = (name, TermType.Unknown, term) :: termTrees
  }

  def addTrees(list: List[(String, TermType.Value, Tree[_])]) {
    termTrees = list ::: termTrees
  }

  def addDefinitions(defs: Map[HOLExpression, HOLExpression]) {
    val map = proofdb.Definitions ++ defs
    proofdb = new ProofDatabase(map, proofdb.proofs, proofdb.axioms, proofdb.sequentLists)
  }

  def getDefinitions: List[(HOLExpression, HOLExpression)] = proofdb.Definitions.toList //._1.toList ::: proofdb.Definitions._2.toList ::: proofdb.Definitions._3.toList

  def getSequentLists = proofdb.sequentLists

  def getProofs = proofdb.proofs ::: proofs

  def getProofDB = proofdb

  def getTermTrees = termTrees

  private var proofdb = new ProofDatabase(Map(), Nil, Nil, Nil)
  private var proofs: List[(String, TreeProof[_])] = Nil
  private var termTrees: List[(String, TermType.Value, Tree[_])] = Nil

  object TermType extends Enumeration {
    val ClauseTerm, ProjectionTerm, Unknown = Value
  }
}
