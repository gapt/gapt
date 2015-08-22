/*
 * trees.scala
 *
 */

package at.logic.gapt.utils.ds.mutable.trees

// V is a vertex - a set of clauses

class TreeNode[V]( var seqList: List[V] ) {
  val nLine = sys.props( "line.separator" )
  var children: Map[Int, TreeNode[V]] = Map()
  def print: Unit = { println( nLine + nLine + "TreeNode:" + nLine + "seqList  = " + seqList.toString ); printMap }
  def printMap: Unit = {
    Console.print( "children = { " )
    children.foreach( child => println( child._1.toString + "  -->  " + child._2.toString ) )
    println( "}" )
  }
}

class Trie[V]( val seqSet: List[V], val features: List[V => Int] ) {
  val nLine = sys.props( "line.separator" )
  var root = new TreeNode( seqSet )
  def print = printTrie( root )

  def printTrie( vert: TreeNode[V] ): Unit = vert.children.size match {
    case 0 => { println( nLine + "leaf = " + vert.seqList.toString ) }
    case _ => {
      println( nLine + "node = " + vert.seqList.toString )
      vert.children.foreach( x => println( nLine + x._1 + "   ->   " + x._2.seqList.toString ) )
      vert.children.foreach( x => printTrie( x._2 ) )
    }
  }

  def isLeaf( vert: TreeNode[V] ): Boolean = {
    vert.children.isEmpty
  }

  def createTree = createTreeRec( root, features )

  private def createTreeRec( vert: TreeNode[V], features: List[V => Int] ): Unit = features match {
    case List() => {
      return
    }
    case _ => {
      vert.seqList.foreach( seq => {
        val key = features.head( seq )
        vert.children.get( key ) match {
          case Some( node ) => {
            val sSet = seq :: node.seqList
            vert.children = vert.children.-( key )
            vert.children = vert.children.+( ( key, new TreeNode( sSet ) ) )
          }
          case _ => vert.children = vert.children.+( ( key, new TreeNode( seq :: Nil ) ) )
        }
      } )
      vert.children.foreach( intTreeNodePair => createTreeRec( intTreeNodePair._2, features.tail ) )
    }
  }
}

