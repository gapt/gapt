/*
 * featureVectorTree.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds.mutable

//import edu.uci.ics.jung.graph.OrderedKAryTree
//import edu.uci.ics.jung.graph.util.EdgeType



  package trees {

  // V is a vertex - a set of clauses
 
  class TreeNode[V](var seqList: List[V]) {
//    var seqList: List[V] = elem
    var children: Map[Int, TreeNode[V]] = Map()
//    def printElem: Unit = { for (x <- elem) }
    def print: Unit = { println("\n\nTreeNode:\nseqList  = "+seqList.toString); printMap }
    def printMap: Unit = {
      Console.print("children = { ")
      children.foreach(child => println(child._1.toString+"  -->  "+child._2.toString))
//      for (x <- children) {
//        println("\n("+x._1)
//        for(s <- x._2.seqList){
//          println("    "+s.toString)
//        }
//        println(")")

     
     
      println("}")
    }
//    def setSeqList(l: List[V]) = { seqList = l }
  }


  class Trie[V](val seqSet: List[V], val features: List[V=>Int]) {

    var root = new TreeNode(seqSet)
    def print = printTrie(root)

    def printTrie(vert: TreeNode[V]): Unit = vert.children.size match{
      case 0 => {println("\nleaf = "+vert.seqList.toString)}
      case _ => {
        println("\nnode = "+vert.seqList.toString)
        vert.children.foreach(x => println("\n"+x._1+"   ->   "+x._2.seqList.toString))
        vert.children.foreach(x => printTrie(x._2))
      }
    }

    def isLeaf(vert: TreeNode[V]): Boolean = {
      vert.children.isEmpty
    }

    def createTree = createTreeRec(root, features)

    private def createTreeRec(vert: TreeNode[V], features: List[V=>Int]): Unit = features match {
//      println("\n createTreeRec\n")
      case List() => {
        println("\nrec bottom\n")
        return }
      case _ => {
     //   val f: (String) => Int = { x => x.split("a").size}
  //      println(vert.seqList)
        println("\nrec part\n")
        vert.seqList.foreach(seq => {
          val key = features.head(seq)
          vert.children.get(key) match {
            case Some(node) => {
              val sSet = seq::node.seqList
              vert.children = vert.children.-(key)
              vert.children = vert.children.+(Pair(key, new TreeNode(sSet)))
            }
            case _ => vert.children = vert.children.+(Pair(key, new TreeNode(seq::Nil)))
          }
        })
        vert.children.foreach(intTreeNodePair => createTreeRec(intTreeNodePair._2, features.tail))
      }
    }
  }
}
//
//
//
//
//        while (i < vert.seqList.size)
//        {
//          if(vert.children.contains(f(vert.seqList(i))))
//          {
//            println("\nwhile if, i = "+i)
//            println("\nvert.children "+vert.children.toString)
//            var newl = vert.seqList(i)::(vert.children.get(f(vert.seqList(i))).get).seqList
//            println("newl = "+newl)
//            vert.children-=f(vert.seqList(i))
//            vert.children += Tuple2(f(vert.seqList(i)), new TreeNode(newl))
//            println("\nvert.children "+vert.children.toString)
//          }
//
//          else
//          {
//            println("\n\nwhile else, i = "+i)
//            var newl = vert.seqList(i)::Nil
//            println("\nvert.children "+vert.children.toString)
//            vert.children += Tuple2(f(vert.seqList(i)), new TreeNode(newl))
//            println("\nvert.children "+vert.children.toString)
//          }
//          i = i+1
//        }
//
//        var j: Int = 0;
//        while(j < vert.children.size) {
////          println("\nrec\n")
//          if(vert.children.contains(j))
//            createTreeRec( vert.children(j), features.tail)
//
//          j=j+1
//        }
//      }
//    }
//  }
//}
