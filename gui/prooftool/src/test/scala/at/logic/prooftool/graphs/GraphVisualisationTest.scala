package at.logic.prooftool.graphs

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

class GraphVisualisationTest extends SpecificationWithJUnit {
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

    //skip("this takes a lot of time")
    "Passing of scala graph to JavaViewer works" in {
        val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(
                        new FileInputStream("target" + separator + "test-classes" + separator + "prime1-0.xml.gz")))) with XMLProofDatabaseParser).getProofs()

        val proof = proofs.first
        /*
        // --- output graph to dot format, works but commented out, because it creates additional files in the project
        val writer = new PrintWriter(new java.io.File("primeproof.dot"))
        writer.append(VisualisationUtils.toDotFormat(proof))
        writer.close
         */
      
       // println(VisualisationUtils.toDotFormat(proof))


        var pv = new ProofViewer[SequentOccurrence](proof)
        pv.doTreePlacement()
        //pv.run()
        //Thread.sleep(150000)
        ()
    }
    /*

     "Creation of a JPanel works" should {
     val g1: EmptyGraph[String] = ( )
     val g2: VertexGraph[String] = ("a", g1)
     val g21: VertexGraph[String] = ("b", g2)
     val g3: EdgeGraph[String] = ("a", "b", g21)
     val g4: EdgeGraph[String] = ("a", "c", EdgeGraph("b", "c", VertexGraph("c", g3)))
     val g5 = EdgeGraph("e", "f", VertexGraph("f", VertexGraph("e", EmptyGraph[String])))
     val g6: UnionGraph[String] = (g4, g5)
      

     var gv = new GraphVisualisation[String]
     var frame = gv.buildFrame(g6)
     /* if you want to see something comment the next line in */
     // frame.show(); Thread.sleep(5000)

     ()
     }

     "Placement of Nodes works" should {
     val g1: EmptyGraph[String] = ( )
     val g2: VertexGraph[String] = ("a", g1)
     val g21: VertexGraph[String] = ("b", g2)
     val g3: EdgeGraph[String] = ("a", "b", g21)
     val g4: EdgeGraph[String] = ("a", "c", EdgeGraph("b", "c", VertexGraph("c", g3)))
     val g5 = EdgeGraph("e", "f", VertexGraph("f", VertexGraph("e", EmptyGraph[String])))
     val g6: UnionGraph[String] = (g4, g5)
      

     var gv = new GraphVisualisation[String]
     var jgraph = gv.create(g6)
     VisualisationUtils.placeNodes(jgraph)

     var frame = gv.buildFrame(g6)
     //frame.show()

     frame.invalidate()

     //Thread.sleep(15000)
    

     ()
     }
     */
}
