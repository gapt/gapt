package at.logic.prooftool.graphs

//import at.logic.prooftool.graphs.wrappers._

import org.jgraph._
import org.jgraph.graph._
import javax.swing._
import java.awt.geom._
import java.awt._
import java.util._

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
  GraphConstants.setBounds(cells(1).getAttributes(), new Rectangle2D.Double(20,50,40,20));
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
//  GraphConstants.setBounds(c.getAttributes(), new Rectangle2D.Double(20,20,40,20));
  GraphConstants.setGradientColor(c.getAttributes(), Color.orange);
  GraphConstants.setOpaque(c.getAttributes(), true);
  GraphConstants.setAutoSize(c.getAttributes(), true)

  jg.getGraphLayoutCache().insert(c)  
}


/* wrapper to use java iterators in for statements*/
class IteratorWrapper[A](iter:java.util.Iterator[A])
{
    def foreach(f: A => Unit): Unit = {
        while(iter.hasNext){
          f(iter.next)
        }
    }
}


// small hack to try out vertex placement
object YOffset {
  var offset = 0;
}

/* Mini Vertex and Edge Classes*/

class Vertex(desc : String) extends DefaultGraphCell(desc) {
  var description: String = desc
  //GraphConstants.setResize(getAttributes(), true) //does not work as expected - perhaps it's only about the cell size not it's placement
  //GraphConstants.setAutoSize(getAttributes(), true)

  //GraphConstants.setBounds(getAttributes(), new Rectangle2D.Double(20, 20+YOffset.offset, 40,20))
  //YOffset.offset += 30
			   

  //Console.println("vertex "+ description + " created!")
  
  
  
  def print() { 
    Console.print("vertex description=\"" + description + "\"")
  }
}

class Edge(description : String, v1 : Vertex, v2 : Vertex) extends DefaultGraphCell(description) {
  def print() { 
    Console.print("edge between \""+ v1.description +"\" and \"" + v2.description+"\"") 
  }
}


class GEdgeFactory extends EdgeFactory[Vertex,Edge] {
  def createEdge(v1:Vertex, v2: Vertex) : Edge = { new Edge("edge", v1,v2) }
} 


/* JGrapht Adapter*/

object AdapterApp extends Application {
  implicit def iteratorToWrapper[T](iter:java.util.Iterator[T]):IteratorWrapper[T] = new IteratorWrapper[T](iter)



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

  var graph = new ListenableDirectedGraph( g )

  // create a visualization using JGraph, via the adapter
  var jgraph = new JGraph( new JGraphModelAdapter( graph ) )

  var jf = new JFrame
  jf.getContentPane.add(new JScrollPane(jgraph))
  jf.pack
  jf.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
  jf.setVisible(true)


  var map = jgraph.getGraphLayoutCache().createNestedMap()
//  for (m <- map.values()) {
//    GraphConstants.setAutoSize(m, true)
//  }


  var c = 0
  var it = map.values().iterator()
  var i = null
  while (it.hasNext()) {
    i = it.next() 
    i match {
//      case Map => Console.out.println("map")
      case _   => c += 1;// Console.out.println("_")
    }
//    GraphConstants.setAutoSize(it.next() : Map[Any, Any] , true)
  }
  Console.println("done "+c)
  jgraph.getGraphLayoutCache().edit(map)
  

  // --- main code end

}
