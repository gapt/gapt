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
 
  class TreeNode[V](elem: List[V]) {
    var seqList: List[V] = elem
    var children: Map[Int, TreeNode[V]] = Map()
//    def printElem: Unit = { for (x <- elem) }
    def print: Unit = { println("\n\nTreeNode:\nseqList  = "+seqList.toString); printMap }
    def printMap: Unit = {
      println("children = { ")
      for (x <- children) {
        println("\n("+x._1)
        for(s <- x._2.seqList){
          println("    "+s.toString)
        }
        println(")")
      }
     
     
      println("}")
    }
    def setSeqList(l: List[V]) = { seqList = l }

  }


  class MyTree[V](rootNode: TreeNode[V], features: List[V=>Int]) {
    var root: TreeNode[V] = rootNode

    
    private def print1(vert: TreeNode[V]) :Unit = {
      vert.print
      if (isLeaf(vert)) {
        println("\n\nLeaf")
        vert.print
//        println("\n print vert : ")        
        return;
      }
    //  println(vert.seqList.toString)
      
      for (seq <- vert.children) {
//        println("\nisn't Leaf\n")
        println("\n\nNode")
        vert.print
//        println(seq._1+"   "+print1(seq._2))
        print1(seq._2)
      }

    }

    def print = print1(root)

    def isLeaf(vert: TreeNode[V]): Boolean = {
      vert.children.isEmpty
    }

    def createTree(vert: TreeNode[V]) = createTreeRec(root, features)

    private def createTreeRec(vert: TreeNode[V], features: List[V=>Int]): Unit = {
//      println("\n createTreeRec\n")
    if(features.isEmpty) {
   //     println("\nrec bottom\n")
        return;
      }
      else {
        val f = features.head
     //   val f: (String) => Int = { x => x.split("a").size}
        var i:Int = 0
        println(vert.seqList)
        while (i < vert.seqList.size)
        {
          if(vert.children.contains(f(vert.seqList(i))))
          {
            println("\nwhile if, i = "+i)
            println("\nvert.children "+vert.children.toString)
            var newl = vert.seqList(i)::(vert.children.get(f(vert.seqList(i))).get).seqList
            println("newl = "+newl)
            vert.children-=f(vert.seqList(i))
            vert.children += Tuple2(f(vert.seqList(i)), new TreeNode(newl))         
            println("\nvert.children "+vert.children.toString)
          }

          else
          {
            println("\n\nwhile else, i = "+i)
            var newl = vert.seqList(i)::Nil
            println("\nvert.children "+vert.children.toString)
            vert.children += Tuple2(f(vert.seqList(i)), new TreeNode(newl))
            println("\nvert.children "+vert.children.toString)
          }
          i = i+1
        }

        var j: Int = 0;
        while(j < vert.children.size) {
//          println("\nrec\n")
          if(vert.children.contains(j))
            createTreeRec( vert.children(j), features.tail)

          j=j+1
        }
      }
    }      
  }
}
