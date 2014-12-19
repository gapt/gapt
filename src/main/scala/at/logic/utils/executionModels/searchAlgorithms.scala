package at.logic.utils.executionModels

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Nov 4, 2010
 * Time: 1:44:00 PM
 * To change this template use File | Settings | File Templates.
 */

import collection.mutable.{Queue => MQueue}
import collection.immutable.Queue
import scala.math.Ordering.Implicits._
import at.logic.utils.logging.Logger

package searchAlgorithms {
  trait SearchAlgorithm {
    type T
    protected def init: Unit // called by the algorithm and implemented by some object using it as the object is initialized before the trait
    protected def add(t: T): Unit
    protected def get: Option[T]
  }

  trait BFSAlgorithm extends SearchAlgorithm {
    private val ds: MQueue[T] = new MQueue[T]()
    init // if the object requires the ds to be already existing, then it will not fail now
    protected def add(conf: T): Unit = ds += conf
    protected def get: Option[T] = {
      val res = ds.headOption
      if (res != None) ds.dequeue
      res
    }
  }

  /** A collection that can be used by generic search algorithms like DFS and BFS
    * to store the list of nodes waiting to be expanded.
    *
    * Queue semantics turn the search into a BFS,
    * stack semantics turn it into a DFS.
    * IDBFS and acyclic A* are also possible.
    */
  trait SearchCollection[ElemType] {
    /** Returns the topmost element without changing the collection */
    def topElem : ElemType
    /** Removes the topmost element and returns the resulting collection */
    def popElem : SearchCollection[ElemType]
    /** Puts a new element into the collection */
    def putElem(x:ElemType) : SearchCollection[ElemType]
    /** Returns the size of the collection */
    def size : Int
  }

  /** A stack. Turns the generic search into a DFS. */
  class DFSColl[ElemType](val s: List[ElemType]) extends SearchCollection[ElemType] {
    override def topElem : ElemType = s.head
    override def popElem : DFSColl[ElemType] = new DFSColl[ElemType](s.tail)
    override def putElem(x:ElemType) : DFSColl[ElemType] = new DFSColl[ElemType](x::s)
    override def size = s.size

    def this() = this(List[ElemType]())

    override def toString() : String = s.toString()
  }

  /** A queue. Turns the generic search into a BFS. */
  class BFSColl[ElemType](val s:Queue[ElemType]) extends SearchCollection[ElemType] {
    override def topElem : ElemType = { s.head }
    override def popElem : BFSColl[ElemType] = { new BFSColl[ElemType](s.dequeue._2) }
    override def putElem(x:ElemType) : BFSColl[ElemType] = { new BFSColl[ElemType](s.enqueue(x)) }
    override def size = { s.size }

    def this() = this(Queue[ElemType]())

    override def toString() : String = {
      s.toList.toString()
    }
  }


  /** Used as a node in DFS/BFS for searching through sets.
    * Specifically, the use case is the following:
    *
    * Starting with the empty set as the root node, various supersets
    * up to certain point are still valid elements and one wishes to
    * to get the largest of these supersets.
    *
    * E.g.: trying to perform resolution with as many pairs of variables
    *       as possible; finding a minimal set cover (with minimality corresponding to validity).
    *
    */
  trait SetNode[ElemType] {
    /** The subset of the entire possible set which this node represents.
      */
    def includedElements: List[(ElemType,Int)]
    /** The complement of includedElements, i.e. the elements not yet included in this node.
      */
    def remainingElements: List[(ElemType,Int)]
    /** The subset of remainingElements which only contains elements
      * larger than every element of includedElements. These are the candidates for addition
      * in the successor nodes.
      */
    def largerElements: List[(ElemType,Int)]

    /** Returns a new node to which a given element has been added. 
      */
    def addElem(p:(ElemType,Int)): SetNode[ElemType]
  }


  object SearchAlgorithms extends Logger {


    /** Performs a parameterizable search with with a custom collection and successor function.
      *
      * It is assumed that all nodes with no successors are goal nodes.
      * and that the successor function generates no invalid nodes.
      *
      * @param sc The collection in which to store the nodes. Ex.: a stack creates a DFS, a queue a BFS.
      * @param root The root node of the search.
      * @param succ The successor function which takes a node and generates all valid successors.
      * @return The list of nodes which have no successors (=goal nodes in this context).
      */
    def GenericSearch[NodeType, CollType <: SearchCollection[NodeType]]
        (sc:CollType, root:NodeType, succ:NodeType => List[NodeType]):List[NodeType] = {

      def innerSearch(sc:CollType) : List[NodeType] = {
        //no more nodes to expand => search is finished.
        if (sc.size == 0) { Nil }
        else {
          val succs = succ(sc.topElem)

          //current node has no successors => add it to the list of solutions.
          if (succs == Nil) { (sc.topElem) :: (innerSearch(sc.popElem.asInstanceOf[CollType])) }
          //otherwise, keep searching: generate successors & push them all to the search stack.
          else { innerSearch(succs.foldLeft(sc.popElem.asInstanceOf[CollType])((s, x) => s.putElem(x).asInstanceOf[CollType])) }
        }
      }

      innerSearch(sc.putElem(root).asInstanceOf[CollType])
    }

    /** Performs a parameterizable search with a custom collection and successor function.
      *
      * Nodes which have no successors are abandoned as dead ends; 
      * nodes for which the goal function returns True are added to the list of
      * solutions and not expanded further.
      *
      * @param sc The collection in which to store the nodes. Ex.: a stack creates a DFS, a queue a BFS.
      * @param root The root node of the search.
      * @param succ The successor function which takes a node and generates all valid successors.
      * @param goal
      * @return The list of nodes which have no successors (=goal nodes in this context).
      */
    def GenericSearch[NodeType, CollType <: SearchCollection[NodeType]]
        (sc:CollType, root:NodeType, succ:NodeType => List[NodeType], goal:NodeType => Boolean):List[NodeType] = {
      def innerSearch(sc:CollType) : List[NodeType] = {
        //no more nodes to expand => search is finished.
        if (sc.size == 0) { Nil }
        else {
          //Current node is goal => don't expand and add to the list of found solutions.
          if (goal(sc.topElem)) {
            sc.topElem :: innerSearch(sc.popElem.asInstanceOf[CollType])
          //else generate its successors and continue searching
          } else {
            val succs = succ(sc.topElem)
            innerSearch(succs.foldLeft(sc.popElem.asInstanceOf[CollType])((s, x) => s.putElem(x).asInstanceOf[CollType]))
          }
        }
      }

      innerSearch(sc.putElem(root).asInstanceOf[CollType])
    }

    /** Performs a parameterizable DFS with a custom successor function.
      * See GenericSearch.
      */
    def DFS[NodeType](root:NodeType, succ:NodeType => List[NodeType]):List[NodeType] = {
      GenericSearch[NodeType, DFSColl[NodeType]](new DFSColl[NodeType](), root, succ)
    }

    /** Performs a parameterizable DFS with a custom successor function.
      * See GenericSearch.
      */
    def DFS[NodeType](root:NodeType, succ:NodeType => List[NodeType], goal:NodeType => Boolean):List[NodeType] = {
      GenericSearch[NodeType, DFSColl[NodeType]](new DFSColl[NodeType](), root, succ, goal)
    }

    /** Performs a parameterizable BFS with a custom successor function.
      * See GenericSearch.
      */
    def BFS[NodeType](root:NodeType, succ:NodeType => List[NodeType]):List[NodeType] = {
      GenericSearch[NodeType, BFSColl[NodeType]](new BFSColl[NodeType](), root, succ)
    }

    /** Performs a parameterizable BFS with a custom successor function.
      * See GenericSearch.
      */
    def BFS[NodeType](root:NodeType, succ:NodeType => List[NodeType], goal:NodeType => Boolean):List[NodeType] = {
      GenericSearch[NodeType, BFSColl[NodeType]](new BFSColl[NodeType](), root, succ, goal)
    }


    /** A higher-order successor function used to turn the generic DFS into an efficient set search.
      * The successors of a node are all nodes which contain one additional element from set of possible ones.
      * In addition to the default constraints, the user can specify an elemFilter, which restricts
      * the elements that can be added and a nodeFilter, which filters out generater successor nodes according
      * to some arbitrary criterion.
      *
      * See SetNode.
      *
      * @param elemFilter Set elements which fail elemFilter won't be added to the current node's set.
      * @param nodeFilter Generated successor nodes which fail nodeFilter won't be returned by this function.
      * @param node The current node.
      * @param return The list of successors which passed both filters.
      */
    def setSearch[ElemType, NodeType <: SetNode[ElemType]]
        (elemFilter:(NodeType, (ElemType,Int)) => Boolean, nodeFilter: NodeType => Boolean, node:NodeType):List[NodeType] = {
        //Generate candidate successors

        trace("   setSearch: node.largerElements = " + node.largerElements.toList.toString)
        val candidateAdditions = node.largerElements.filter(e => {
            val (elem,index) = e
            !node.includedElements.contains(index) &&
            (node.includedElements.length == 0 || index > node.includedElements.head._2) &&
            elemFilter(node,e)
          })

        trace("              passed filter: " + candidateAdditions.length)

        //Create the successor nodes
        //asInstanceOf: ugly hack, but it wouldn't typecheck otherwise
        val candidateNodes = candidateAdditions.map(x => node.addElem(x).asInstanceOf[NodeType])

        //Filter according to postFilter
        candidateNodes.filter(node => nodeFilter(node))
    }
  }
}
