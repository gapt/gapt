package at.logic.prooftool.graphs

//import at.logic.prooftool.graphs.wrappers._

import org.jgraph._
import org.jgraph.graph._
import javax.swing._
import java.awt.geom._
import java.awt._

import org.jgrapht._
import org.jgrapht.ext._
import org.jgrapht.graph._


/**
 * Hello world!
 *
 */
object JGraphApp extends Application {
  var jf = new JFrame
  var jm = new DefaultGraphModel
  var cache = new GraphLayoutCache(jm, new DefaultCellViewFactory)
  var jg = new JGraph (jm, cache)
  
  var cells = new Array[DefaultGraphCell](3)
  cells.update(0, new DefaultGraphCell(new String("cell 1") ))
  
  GraphConstants.setBounds(cells.apply(0).getAttributes(), new Rectangle2D.Double(20,20,40,20));
  GraphConstants.setGradientColor(cells.apply(0).getAttributes(), Color.orange);
  GraphConstants.setOpaque(cells.apply(0).getAttributes(), true);

  
  cells.update(1, new DefaultGraphCell(new String("cell 2") ))
  GraphConstants.setBounds(cells(1).getAttributes(), new Rectangle2D.Double(20,20,40,20));
  GraphConstants.setGradientColor(cells(1).getAttributes(), Color.orange);
  GraphConstants.setOpaque(cells(1).getAttributes(), true);
  
  var port0 = new DefaultPort
  var port1 = new DefaultPort
  
  cells(0).add(port0)
  cells(1).add(port1)
  
  var edge = new org.jgraph.graph.DefaultEdge("edge")
  edge.setSource(cells(0).getChildAt(0))
  edge.setTarget(cells(1).getChildAt(0))
  
  cells(2) = edge
  
    
  for (c <- cells) {
    jg.getGraphLayoutCache().insert(c)
  }

  // jg.getGraphLayoutCache().insert(cells) // adding the whole array does only work in java!

  
  jf.getContentPane.add(new JScrollPane(jg))
  jf.pack
  jf.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
  jf.setVisible(true)

  var c = new DefaultGraphCell(new String("cell 3") )
  GraphConstants.setBounds(c.getAttributes(), new Rectangle2D.Double(20,20,40,20));
  GraphConstants.setGradientColor(c.getAttributes(), Color.orange);
  GraphConstants.setOpaque(c.getAttributes(), true);

  jg.getGraphLayoutCache().insert(c)  
  
  
}


/* Mini Vertex and Edge Classes*/

class Vertex(desc : String) {
  var description: String = desc
  
  def print() { 
    Console.print("vertex description=\"" + description + "\"")
  }
}

class Edge(description : String, v1 : Vertex, v2 : Vertex) {
  def print() { 
    Console.print("edge between \""+ v1.description +"\" and \"" + v2.description+"\"") 
  }
}


class GEdgeFactory extends EdgeFactory[Vertex,Edge] {
  def createEdge(v1:Vertex, v2: Vertex) : Edge = { new Edge("edge", v1,v2) }
} 


/* JGrapht Adapter*/

object AdapterApp extends Application {
  var v1 = new Vertex("v1")
  var v2 = new Vertex("v2")
  var v3 = new Vertex("v3")
  var v4 = new Vertex("v4")
  var v5 = new Vertex("v5")
  var e  = new Edge("e",v1,v2)
  e.print()
  Console.println()
  
  var factory = new GEdgeFactory
  
  var g = new DefaultDirectedGraph[Vertex,Edge](factory)
  g.addVertex(v1)
  g.addVertex(v2)
  g.addVertex(v3)
  g.addVertex(v4)
  g.addVertex(v5)
  g.addEdge(v1,v2)
  g.addEdge(v2,v4)
  g.addEdge(v2,v3)
  g.addEdge(v3,v5)

  //Console.print(g.toString())

  // create a JGraphT graph
  /* scala does not see the ListenableDirectedGraph(java.lang.Class) constructor,
     solve via java wrapper hiding the copy constructor?
   */
  // var graph = new ListenableDirectedGraph( classOf[org.jgrapht.graph.DefaultEdge] )

  // create a visualization using JGraph, via the adapter
//  var jgraph = new JGraph( new JGraphModelAdapter( graph ) )



}