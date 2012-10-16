/**
 * This file contains an algebraic definition of a labeled tree. This differs from the trees package in the ds folder
 * with regard that it is not based on graphs by inheritance but on algebraic data types like other data structures in
 * the scala library.
 * The user is responsible to make sure that the tree is not an acyclic graph.
 */

package at.logic.utils.ds.algebraic

import at.logic.utils.ds.trees.{TreeA,NonTerminalNodeA,TerminalNodeA}

package trees {
  trait Tree[+V,+E] extends TreeA[V,E]{
    def node: V
  }

  case class TerminalNode[+V,+E](node: V) extends Tree[V,E] with TerminalNodeA[V,E]
  case class NonTerminalNode[+V,+E](node: V, children: Seq[Tuple2[Tree[V,E],E]]) extends Tree[V, E] with NonTerminalNodeA[V,E]
}
