package at.logic.prooftool.graphs

import org.jgraph._
import org.jgraph.graph._
import org.jgrapht._
import org.jgrapht.graph._
import javax.swing._
import java.awt.geom._
import java.awt._


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

/**
 * Hello world!
 *
 */
object App extends Application {
  
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

  Console.print(g.toString())
  
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
  
  var port0 = new DefaultPort
  var port1 = new DefaultPort
  
  cells.apply(0).add(port0)
  cells.apply(1).add(port1)
  
  var edge = new org.jgraph.graph.DefaultEdge
  edge.setSource(cells.apply(0).getChildAt(0))
  edge.setSource(cells.apply(1).getChildAt(0))
  
  Console.println()
  Console.println("edge="+edge.getTarget() )
  if (edge==null)  {
    Console.println("!!!")
    }
  else {
    Console.println("!= null");
  }
  
  cells.update(2, edge)
  
  Console.println()
  for (c <- cells) {
    Console.println(c)
    
  }
  
  Console.println(cells)
  
  jg.getGraphLayoutCache().insert(cells)
  
  jf.getContentPane.add(new JScrollPane(jg))
  jf.pack
  jf.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
  jf.setVisible(true)
  
}
