/*
 * FeatureVectorIndexingManager.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption.managers

import at.logic.utils.ds.mutable.trees._
import at.logic.calculi.lk.base._
import at.logic.algorithms.subsumption._




//val a = new VectorTreeManager with StillmabAlgorithm {val seqList = }
trait VectorTreeManager extends SubsumptionAlgorithm  {

  var seqList: List[Sequent]
  var features: List[Sequent=>Int]
  var tree: Trie[Sequent]


  def forwardSubsumption

  def forwardSubsumptionRec(vert: TreeNode[Sequent], features: List[Sequent=>Int], subsumedSeq: Sequent): Boolean = {

//    if(tree.isLeaf(vert)) {
    if(features.isEmpty) {
      println("\n\nLeaf:  "+subsumedSeq+"   <--->   ");
      vert.print
      vert.seqList.exists(seq => {
        val x = subsumes(subsumedSeq, seq);
        if (x) Console.println(x);
        x;
      })
//      for(seq <- vert.seqList) {
//        if(subsumes(subsumedSeq, seq)) {
//          println("The clause  is subsumed ! \n\n")
//          return true
//        }
//      }
//      return false
    } else
    {
    println("\nvert = ")
    vert.print
    println("\n\nfeature vector of the subsumedSeq = "+features.head(subsumedSeq))

    vert.children.exists(child => child._1 <= features.head(subsumedSeq) && forwardSubsumptionRec(child._2, features.tail, subsumedSeq))

//    for (child <- vert.children)
//    {
//      if(child._1 <= features.head(subsumedSeq))
//        if (forwardSubsumption1(child._2, features.tail, subsumedSeq))
//          return true
//    }
//    println("\n\n    false \n\n")
//    return false
    }
  }
}

