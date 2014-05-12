/*
 * FeatureVectorIndexingManager.scala
 *
 */

/* Never used
package at.logic.algorithms.subsumption.managers

import at.logic.utils.ds.mutable.trees._
import at.logic.calculi.lk.base.FSequent
import at.logic.algorithms.subsumption._

trait VectorTreeManager extends SubsumptionAlgorithm  {

  var seqList: List[FSequent]
  var features: List[FSequent=>Int]
  var tree: Trie[FSequent]

  def forwardSubsumption

  def forwardSubsumptionRec(vert: TreeNode[FSequent], features: List[FSequent=>Int], subsumedSeq: FSequent): Boolean = {
    if(features.isEmpty) {
      vert.seqList.exists( seq => subsumes(subsumedSeq, seq) )
    } else {
      vert.children.foreach(child => 
        if (child._1 <= features.head(subsumedSeq) && forwardSubsumptionRec(child._2, features.tail, subsumedSeq)) 
          return true
      )
      return false
    }
  }
}
*/

