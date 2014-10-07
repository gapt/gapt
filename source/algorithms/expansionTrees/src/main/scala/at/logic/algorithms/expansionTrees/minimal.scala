package at.logic.algorithms.expansionTrees

import at.logic.provers.Prover
import scala.collection.mutable.{Stack, HashSet, ListBuffer}
import at.logic.calculi.expansionTrees.multi._
import at.logic.utils.dssupport.ListSupport.{listComplements, zipper, pairwiseImages}
import at.logic.calculi.expansionTrees.{ExpansionTree, ExpansionSequent}

/** Given a MultiExpansionSequent S and a prover P, this algorithm returns a list of the minimal expansion sequents below or equal to S that P still evaluates as valid.

*/
object minimalExpansionSequents {
  
  def apply(sequent: MultiExpansionSequent, prover: Prover) : Seq[MultiExpansionSequent] = {
    val result= new HashSet[MultiExpansionSequent] // The list of minimal expansion proofs will be constructed iteratively. A HashSet is used so that duplicates are immediately disregarded.
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
    
    result.toSeq
  }
  
  def apply(sequent: ExpansionSequent, prover: Prover): Seq[ExpansionSequent] = minimalExpansionSequents(compressQuantifiers(sequent), prover).map(decompressQuantifiers.apply)
  
  /** Given a MultiExpansionSequent, this generates all sequents obtained by removing one instance from one tree.
    *
    */
  def generateSuccessors(sequent: MultiExpansionSequent): Seq[MultiExpansionSequent] = sequent match {
    case MultiExpansionSequent(ant, suc) => {
      var newSequents = new ListBuffer[MultiExpansionSequent] //newSequents will be the list of expansion sequents obtained from S by removing one instance from one tree of S.
      for (j <- 1 to ant.length) {
        val (tree, fst, snd) = zipper(ant, j) //We iteratively focus each expansion tree in the antecedent of S.
        val newTrees = generateSuccessorTrees(tree)
        newSequents ++= newTrees.map(t => MultiExpansionSequent(fst ++ Seq(t) ++ snd, suc))
      }
          
      for (j <- 1 to suc.length) { //This for loop is analogous to the one for the antecedent.
        val (tree, fst, snd) = zipper(suc, j)
        val newTrees = generateSuccessorTrees(tree)
        newSequents ++= newTrees.map(t => MultiExpansionSequent(ant, fst ++ Seq(t) ++ snd))
      }
          
      newSequents.toSeq
    }
  }
  
  /** Given a MultiExpansionTree, this produces all trees obtained by erasing exactly one instance.
    *
    */
  def generateSuccessorTrees(tree: MultiExpansionTree): Seq[MultiExpansionTree] = tree match {
    case Atom(f) => Nil // This could also be => Atom(f). The way it's written now, quantifier-free trees will have no successors, which makes sense–in effect, they consist of a single instance.
    case Not(s) => generateSuccessorTrees(s).map(Not.apply)
    case And(left, right) => {
      val sLeft = generateSuccessorTrees(left)
      val sRight = generateSuccessorTrees(right)
      sLeft.map(t => And(t, right)) ++ sRight.map(t => And(left,t)) 
    }
    case Or(left, right) => {
      val sLeft = generateSuccessorTrees(left)
      val sRight = generateSuccessorTrees(right)
      sLeft.map(t => Or(t, right)) ++ sRight.map(t => Or(left,t))
    }
    case Imp(left, right) => {
      val sLeft = generateSuccessorTrees(left)
      val sRight = generateSuccessorTrees(right)
      sLeft.map(t => Imp(t, right)) ++ sRight.map(t => Imp(left,t))
    }
          
    case StrongQuantifier(f, vars, sel) => generateSuccessorTrees(sel).map(StrongQuantifier.apply(f,vars,_))
    case SkolemQuantifier(f, vars, sel) => generateSuccessorTrees(sel).map(SkolemQuantifier.apply(f,vars,_))
       
    case WeakQuantifier(f, inst) => {
      if (!containsWeakQuantifiers(inst.head._1)) { //In this case we are in a bottommost weak quantifier node, which means that we will actually remove instances.
        if (inst.length > 1) {  
          val instances = listComplements(inst) //These two lines generate all expansion trees that result from removing an instance from tree.
          instances.map(i => WeakQuantifier(f,i))          
        }
        else Nil
      }
      else inst.map(p => generateSuccessorTrees(p._1)).flatten
    }
  }
  
  def containsWeakQuantifiers(tree: MultiExpansionTree): Boolean = tree match {
    case Atom(f) => false
    case And(left, right) => containsWeakQuantifiers(left) || containsWeakQuantifiers(right)
    case Or(left, right)  => containsWeakQuantifiers(left) || containsWeakQuantifiers(right)
    case Imp(left, right) => containsWeakQuantifiers(left) || containsWeakQuantifiers(right)
    case Not(s) => containsWeakQuantifiers(s)
    case StrongQuantifier(_,_,sel) => containsWeakQuantifiers(sel)
    case SkolemQuantifier(_,_,sel) => containsWeakQuantifiers(sel)
    case WeakQuantifier(_,_) => true
  }
}