package at.logic.prooftool.graphs
  /*
import at.logic.utils.ds._

import org.jgraph.JGraph
import org.jgraph.graph.AttributeMap
import org.jgraph.graph.GraphLayoutCache

import javax.swing._
import java.awt.geom._
import java.awt._
import java.util._

import org.jgrapht._
import org.jgrapht.ext._
import org.jgrapht.graph._

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._

import at.logic.utils.ds.graphs._
import GraphImplicitConverters._
import at.logic.prooftool.ProofViewer

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import java.io.{PrintWriter, FileReader, FileInputStream, InputStreamReader}
import java.util.zip.GZIPInputStream
import java.io.File.separator

object VisualisationUtils {
  /* */
    //TODO: A Proof is no Graph anymore -> will fix
    def main(args: Array[String]) {

      println("This is package at.logic.prooftool.graphs.VisualsationUtils main method!")
      val reader = (new XMLReader(new InputStreamReader(new GZIPInputStream(
                        new FileInputStream(args(0))))) with XMLProofDatabaseParser)
      val proofs = reader.getProofDatabase.proofs
      //TODO: the scala infer the inheritance of LKProof from Graph - hotfix: giving tpe by hand
      // remark by daniel: changed proofs.first to proofs.first._2
      //                   proofs.first._1 contains the name of the proof
      // end remark
        val proof : at.logic.utils.ds.graphs.Graph[Sequent] = proofs.first._2
        //var pv = new ProofViewer[Sequent](proof)
        //pv.doTreePlacement()
        //pv.run()
    }
    /* */

    //generates a binary tree of given depth and name of parent label. subsequnt nodes will get
    // the character l or r prepended depending wether they went _l_eft ot _r_ight
    def createTree(label:String, depth : Int) : at.logic.utils.ds.graphs.Graph[String] = {
        if (depth <= 0) {
            graphs.VertexGraph[String](label, graphs.EmptyGraph[String])
        } else {
            var label1 = "l"+label
            var label2 = "r"+label
            var tree1 = createTree(label1, depth-1)
            var tree2 = createTree(label2, depth-1)
/*
            var g : graphs.Graph[String] = graphs.VertexGraph(label,graphs.UnionGraph(tree1,tree2))
            g = graphs.EdgeGraph[String](label,label1,g )
            g = graphs.EdgeGraph[String](label,label2,g )
            g
*/
            graphs.VertexGraph[String](label, graphs.EmptyGraph[String])
        }
    }


    // formats a graph to dot format (http://graphviz.org)
  /*
    def toDotFormat(g : graphs.Graph[Sequent]) : String = {
        var sb = new scala.StringBuilder()
        var m = new scala.collection.mutable.HashMap[Sequent,Int]()

        sb.append("digraph g { \n")
        // output vertices
        val vs = g.graph.vertexSet()
        val it = vs.iterator
        var v: Sequent = null
        var i = 0
            
        while (it.hasNext) {
            v = it.next
            m.put(v,i)
//            sb.append("\tv"+i+ " [label=\""+SequentFormatter.sequentToString(v.getSequent)+"\"];\n")
            sb.append("\tv"+i+ " [label=\""+v.getSequent+"\"];\n")
            i += 1
        }

        sb.append("\n")
        // output edges
        val es = g.graph.edgeSet()
        val it2 = es.iterator
        var e: DefaultEdge[Sequent] = null
        i = 0

      var targetset = new HashSet[Int]
      var sourceset = new HashSet[Int]

        while (it2.hasNext) {
            e = it2.next
            (m.get(g.graph.getEdgeSource(e)), m.get(g.graph.getEdgeTarget(e))) match {
              case (Some(src), Some(trg)) =>
                sb.append("\t v"+src + " -> v"+ trg + ";\n")
                sourceset.add(src)
                targetset.add(trg)

              case _ => ;
            }
            i += 1
        }

      //println("roots=" + (vs.size-sourceset.size) + " leafs="+ (vs.size-targetset.size))

      /*
      var rootset = new HashSet[Int]
      var c :Int = 0
      while (c<i) {
        rootset.add(c)
        c += 1
      }
  
      rootset.removeAll(sourceset)
      println(rootset)
      */

        sb.append("\n}\n")
        

        sb.toString
    }
   */

}
*/
