package at.logic.prooftool.graphs

//import at.logic.prooftool.graphs.wrappers._

import at.logic.utils.ds._

import org.jgraph._
import org.jgraph.graph._
import javax.swing._
import java.awt.geom._
import java.awt._
import java.util._

import org.jgrapht._
import org.jgrapht.ext._
import org.jgrapht.graph._



class GraphVisualisation[T] {

  /* shows a frame with the graph*/
  def show(g :  at.logic.utils.ds.graphs.Graph[T]) = {
    var jf = buildFrame(create(g))
    jf.setVisible(true)
    
  }

  /* calls create and puts the jgraph into a frame */
  def buildFrame(g : at.logic.utils.ds.graphs.Graph[T]) : JFrame = buildFrame(create(g))

  def buildFrame(g : JGraph) : JFrame = {
    var jf = new JFrame
    jf.getContentPane.add(new JScrollPane(g))
    jf.pack
    jf.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)

    return jf;
  }

  /* creates a jgraph from out graph model */
  def create(g : at.logic.utils.ds.graphs.Graph[T]) : JGraph = {
    if (! g.graph.isInstanceOf[ListenableGraph[Any,Any]])
      throw new Exception("Excpecting a Listenable Graph in the at.logic.utils.ds.graph model!")

    var jgraph = new JGraph( new JGraphModelAdapter( g.graph ) )
    return jgraph;
  }

}

object VisualisationUtils {
  def createTree(label:String, depth : Int) : at.logic.utils.ds.graphs.Graph[String] = {
      if (depth <= 0) {
          graphs.VertexGraph[String](label, graphs.EmptyGraph[String])
      } else {
          var label1 = "l"+label
          var label2 = "r"+label
          var tree1 = createTree(label1, depth-1)
          var tree2 = createTree(label2, depth-1)

          var g : graphs.Graph[String] = graphs.VertexGraph(label,graphs.UnionGraph(tree1,tree2))
          g = graphs.EdgeGraph[String](label,label1,g )
          g = graphs.EdgeGraph[String](label,label2,g )
          g
      }
  }

  def placeNodes(jgraph : JGraph) = {
    // hm this should work, shouldn't it?
    Console.println("placement")


    var cache : GraphLayoutCache  = jgraph.getGraphLayoutCache();
    var m  = cache.createNestedMap();
    var it  = m.values().iterator();
    var i : Any = null;

    while (it.hasNext()) {
      i = it.next();

      if (i.isInstanceOf[Map[Any,Any] ]) {
        var im  = i.asInstanceOf[Map[Any,Any] ];
	var j : Any = null;
	var it2 = im.values().iterator()

        while (it2.hasNext() ) {
	  j = it2.next();

          if (j.isInstanceOf[AttributeMap.SerializableRectangle2D]) {
            var  r :Rectangle2D.Double = j.asInstanceOf[AttributeMap.SerializableRectangle2D];
            r.x = 10.0;
            r.y = 400.0;
            r.width = 100.0;
            r.height = 50.0;
            Console.println("setting new rectangle:"+r.toString());
          }
        }
      }
    }

    Console.println("cache partial? "+cache.isPartial)
            
    cache.edit(m);
  }
}



//    var map = cache.createNestedMap()
//
////    Console.print(map)
//    var c = 0
//    var it = map.values().iterator()
//    var i : Any = null
//
//    var x_ : Double = 200
//    var y_ : Double = 200
//
    

//    while (it.hasNext()) {
//      i = it.next()
//      if (i.isInstanceOf[Map[Any,Any]]) {
////      try {
//	Console.print("Found an Attribute Map:")
//	var m = i.asInstanceOf[Map[Any,Any]]
//	//Console.print(m)
//	var rect : Rectangle2D.Double  = GraphConstants.getBounds(m).asInstanceOf[Rectangle2D.Double]
//	if (rect != null) {
//	  rect.setRect(x_ ,y_ , rect.width, rect.height)
//	  y_ += 50
//
//	  //Console.print(rect)
//	  GraphConstants.setBounds(m,rect)
//	  //Console.println(m)
//	}
//	()
//      } else {
//	if (i.isInstanceOf[AnyRef]) {
//	  val ar = i.asInstanceOf[AnyRef];
//	  Console.println("skipping..."+ ar.getClass );
//	} else {
//	  Console.println("skipping...");
//	}
//      }

////      Console.println(map)
////      cache.edit(map)
////      Console.println("   ---- ")
////      Console.println(cache.createNestedMap())
////  }
//}


// --- only tests from here on ---

object PlacementTestApp extends Application {
import at.logic.utils.ds.graphs._
import GraphImplicitConverters._

    override def main(args : Array[String]) {
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
    frame.show()
    }
}

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
//  while (it.hasNext()) {
//    i = it.next() 
//    i match {
////      case Map => Console.out.println("map")
//      case _   => c += 1;// Console.out.println("_")
//    }
////    GraphConstants.setAutoSize(it.next() : Map[Any, Any] , true)
//  }
//  Console.println("done "+c)
  jgraph.getGraphLayoutCache().edit(map)
  

  // --- main code end

}
