package at.logic.gui.prooftool.parser

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 5, 2010
 * Time: 3:00:53 PM
 */

import scala.swing._
import event.ValueChanged
import java.io.{FileInputStream, InputStreamReader}
import at.logic.parsing.language.xml.XMLParser.XMLProofDatabaseParser
import at.logic.parsing.readers.XMLReaders._
import at.logic.calculi.lk.base._
import at.logic.parsing.language.xml.ProofDatabase

class FileParser {

  def fileReader(f: String): LKProof = try {
    proofdb = (new XMLReader(new InputStreamReader(new FileInputStream(f))) with XMLProofDatabaseParser).getProofDatabase()
    proofNames = proofdb.proofs.map( x => x._1)
    proofDbChanged.publish(new ValueChanged(new Label("New DB is loaded")))
    proofdb.proofs.head._2
  } catch {
      case e: AnyRef =>
        import Dialog._
        val t = e.toString
        showMessage(new Label(t),"Couldn't load file: "+f+"!\n\n"+t.replaceAll(",","\n"))
        proofDbChanged.publish(new ValueChanged(new Label("New DB can't be loaded")))
        proofdb.proofs.head._2
  }

  def displayProof(f: LKProof, step: Int): String = f match {
    case p: UnaryLKProof => p.root.toString+"\n "+p.rule+step+": \n"+displayProof(p.uProof, step+1)
    case p: BinaryLKProof => p.root.toString+"\n first branch of "+p.rule+step+": \n"+displayProof(p.uProof1, step*10+1)+"\n second branch of "+p.rule+step+": \n"+displayProof(p.uProof2, step*10+1)
    case _ =>  f.root.toString
  }

  def getDB = proofdb
  def getProofNames = proofNames

  private var proofdb =  new ProofDatabase(Nil,Nil,Nil)
  private var proofNames: List[String] = Nil
}

object proofDbChanged extends Publisher