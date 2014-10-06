package at.logic.algorithms.expansionTrees

import at.logic.provers.Prover
import scala.collection.mutable.{Stack, HashSet, ListBuffer}
import at.logic.calculi.expansionTrees.multi._
import at.logic.utils.dssupport.ListSupport.{listComplements, zipper}

/** Given a MultiExpansionSequent S and a prover P, this algorithm returns a list of the minimal expansion sequents below or equal to S that P still evaluates as valid.

*/
object minimalExpansionSequents {
  
  def apply(sequent: MultiExpansionSequent, prover: Prover) : List[MultiExpansionSequent] = {
    val result= new HashSet[MultiExpansionSequent] // The list of minimal expansion proofs will be constructed iteratively.
    val stack = new Stack[MultiExpansionSequent] // Invariant: the stack only contains tautological expansion sequents.
    
    if (prover.isValid(sequent.toDeep))
      stack.push(sequent) // The sequent under consideration is placed on the stack if it is tautological.
    
    while (!stack.isEmpty) {
      var current = stack.pop() // Topmost element of stack is retrieved. We already know it is tautological; only need to consider its successors.
      var newSequents = generateSuccessors(current) // All successor expansion sequents are generated.
      var minimal = true // We assume that the current sequent is minimal unless we prove otherwise.
      
      for (s <- newSequents) { // Iterate over the generated successors
        if (prover.isValid(s.toDeep)) {
          stack.push(s) // Push valid sequents on the stack
          minimal = false // If there is a valid sequent below the current one, it is not minimal.
        }
      }
      
      if (minimal)
        result += current // If the current sequent is minimal, we add it to the results.
    }
    
    result.toList
  }
  
  def generateSuccessors(sequent: MultiExpansionSequent): List[MultiExpansionSequent] = sequent match {
    case MultiExpansionSequent(ant, suc) => {
      var newSequents = new ListBuffer[MultiExpansionSequent] //newSequents will be the list of expansion sequents obtained from S by removing one instance from one tree of S.
      for (j <- 1 to ant.length) {
        val (tree, fst, snd) = zipper(ant.toList, j) //We iteratively focus each expansion tree in the antecedent of S.
        tree match {
          case WeakQuantifier(f, inst) => {
            if (inst.length > 1) {  
              val instances = listComplements(inst.toList) //These two lines generate all expansion trees that result from removing an instance from tree.
              val newTrees = instances.map(i => WeakQuantifier(f,i))
              newSequents ++= newTrees.map(t => MultiExpansionSequent(fst ++ List(t) ++ snd, suc))
            }
          }

          case _ =>
        }
      }
          
      for (j <- 1 to suc.length) { //This for loop is analogous to the one for the antecedent.
        val (tree, fst, snd) = zipper(suc.toList, j)
        tree match {
          case WeakQuantifier(f, inst) => {
            if (inst.length > 1) {
              val instances = listComplements(inst.toList)
              val newTrees = instances.map(i => WeakQuantifier(f,i))
              newSequents ++= newTrees.map(t => MultiExpansionSequent(ant, fst ++ List(t) ++ snd))
            }
          }
              
          case _ =>
        }
      }
          
      newSequents.toList
    }
  }
}