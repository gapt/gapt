package at.logic.prooftool.graphs
   /*
import org.specs._
import org.specs.runner._

import at.logic.utils.ds.graphs._
import GraphImplicitConverters._
import at.logic.prooftool.ProofViewer

import java.util.zip.GZIPInputStream
import java.io.File.separator
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import java.io.{PrintWriter, FileReader, FileInputStream, InputStreamReader}
import scala.collection.immutable.HashSet
import scala.swing._
import at.logic.prooftool.formuladrawing.FormulaLabel
import java.awt.geom.Rectangle2D
import java.awt.Dimension

class GraphVisualisationTest extends SpecificationWithJUnit {
  val showWindow = false

    "formula parsing works" in {
      val f = new Frame
      val l = new FormulaLabel
      l text = "a^bc_de_{fg}hijk^{lm}{no}"
      f contents = l
      f size = new Dimension(400,400)
      if (showWindow) {
        f visible = true
        Thread.sleep(10000)
      }
      ()
    }

  /*
     "Showing Formulas works" in {
        val reader = (new XMLReader(new InputStreamReader(new GZIPInputStream(
                        new FileInputStream("target" + separator + "test-classes" + separator + "prime1-0.xml.gz")))) with XMLProofDatabaseParser)

        val proofs = reader.getProofDatabase.proofs

        //TODO: scala does not infer the inheritance of LKProof from Graph - hotfix: giving type by hand
        val proof : at.logic.utils.ds.graphs.Graph[SequentOccurrence] = proofs.first
         val f = new Frame
         val scrollpane = new ScrollPane
         val panel = new BoxPanel( Orientation.Vertical )
         f contents_= scrollpane
         scrollpane contents_= panel

         var it = proof.graph.vertexSet.iterator
         while (it.hasNext) {
           val l = new FormulaLabel
           l text_= it.next.toString
           l size_= new Dimension(300,150)
           l visible_= true
           panel.contents += l
         }
          scrollpane visible_= true
       
          //f size = new Dimension(400,400)
          //f visible = true
          //panel.revalidate
          //pThread.sleep(500000)
        ()
      }
*/      


  /*
    "Passing of scala graph to JavaViewer works" in {
        val g1: EmptyGraph[String] = ( )
        val g2: VertexGraph[String] = ("a", g1)
        val g21: VertexGraph[String] = ("b", g2)
        val g3: EdgeGraph[String] = ("a", "b", g21)
        val g4: EdgeGraph[String] = ("a", "c", EdgeGraph("b", "c", VertexGraph("c", g3)))
        val g5 = EdgeGraph("e", "f", VertexGraph("f", VertexGraph("e", EmptyGraph[String])))
        val g6: UnionGraph[String] = (g4, g5)

        val tree = VisualisationUtils.createTree("x",8)
        var pv = new ProofViewer[String](tree)
        //pv.insertLotsOfCells()
        pv.doTreePlacement()
        //pv.run()
        //Thread.sleep(150000)
        ()
    }
    */

  /*
    //skip("this takes a lot of time")
    "Passing of prime proof to JavaViewer works" in {
        val reader = (new XMLReader(new InputStreamReader(new GZIPInputStream(
                        new FileInputStream("target" + separator + "test-classes" + separator + "prime1-0.xml.gz")))) with XMLProofDatabaseParser)

        val proofs = reader.getProofDatabase.proofs

        //TODO: scala does not infer the inheritance of LKProof from Graph - hotfix: giving type by hand
        val proof : at.logic.utils.ds.graphs.Graph[SequentOccurrence] = proofs.first
        /*
        // --- output graph to dot format, works but commented out, because it creates additional files in the project
        val writer = new PrintWriter(new java.io.File("primeproof.dot"))
        writer.append(VisualisationUtils.toDotFormat(proof))
        writer.close
         */
      
       // println(VisualisationUtils.toDotFormat(proof))


        var pv = new ProofViewer[SequentOccurrence](proof)
        pv.doTreePlacement()
        if (showWindow) {
          pv.run()
          Thread.sleep(150000)
        }
        ()
    }
    */
}
*/