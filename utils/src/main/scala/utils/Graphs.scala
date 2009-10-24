/*
 * Graphs.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils

object Graphs {
    
    case class Graph[V]() extends org.jgrapht.graph.DefaultDirectedGraph[V,org.jgrapht.graph.DefaultEdge](classOf[org.jgrapht.graph.DefaultEdge])

    // this version has an arbitrary edge type but I am not sure we need it. What do you think?
    //case class Graph[V <: AnyRef, E <: AnyRef](implicit m: scala.reflect.Manifest[E]) extends org.jgrapht.graph.DefaultDirectedGraph[V,E](m.erasure.asInstanceOf[java.lang.Class[E]] )
}
