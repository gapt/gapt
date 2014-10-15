package at.logic.algorithms.expansionTrees

import at.logic.provers.Prover
import scala.collection.mutable.{Stack, HashSet, ListBuffer, HashMap => mMap}
import at.logic.calculi.expansionTrees.multi._
import at.logic.utils.dssupport.ListSupport.{listComplements, zipper}
import at.logic.utils.dssupport.MapSupport.addNoOverwrite
import at.logic.calculi.expansionTrees.{ExpansionTree, ExpansionSequent}
import at.logic.language.hol.HOLExpression
import at.logic.utils.logging.Logger


/** Given a MultiExpansionSequent S and a prover P, this algorithm returns a list of the minimal expansion sequents below or equal to S that P still evaluates as valid.

*/
object minimalExpansionSequents extends Logger {
  
  def apply(sequent: MultiExpansionSequent, prover: Prover) : Seq[MultiExpansionSequent] = {
    val result= new HashSet[MultiExpansionSequent] // The list of minimal expansion proofs will be constructed iteratively. A HashSet is used so that duplicates are immediately disregarded.
    val stack = new Stack[MultiExpansionSequent] // Invariant: the stack only contains tautological expansion sequents.
    
    if (prover.isValid(sequent.toDeep))
      stack.push(sequent) // The sequent under consideration is placed on the stack if it is tautological.
    
    while (!stack.isEmpty) {
      info("Retrieving sequent from stack")
      var current = stack.pop() // Topmost element of stack is retrieved. We already know it is tautological; only need to consider its successors.
      info("Generating successors")
      var newSequents = generateSuccessors(current) // All successor expansion sequents are generated.
      var minimal = true // We assume that the current sequent is minimal unless we prove otherwise.
      
      for (s <- newSequents) { // Iterate over the generated successors
        if (prover.isValid(s.toDeep)) {
          stack.push(s) // Push valid sequents on the stack
          minimal = false // If there is a valid sequent below the current one, it is not minimal.
        }
      }
      
      if (minimal) {
        info("Minimal sequent found.")
        result += current // If the current sequent is minimal, we add it to the results.
      }
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
    case Atom(f) => Nil
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
}

/** An optimized version of minimalExpansionSequents.
  * It's implemented as a class + companion object because the algorithm uses a map that is constructed iteratively and it's convenient to have access to it from arbitrary points.
  */
class minimalExpansionSequentsSmart (val sequent: MultiExpansionSequent, val prover: Prover) extends Logger {
  
  val maxRemovedInstance = new mMap[MultiExpansionSequent,Int] // This assigns to each MultiExpansionSequent S the maximum of all numbers n with the following property: S can be obtained from a MultiExpansionSequent S' by removing the nth instance of S'.
  
  def compute() : Seq[MultiExpansionSequent] = {
    val result= new ListBuffer[MultiExpansionSequent] // The list of minimal expansion proofs will be constructed iteratively.
    val stack = new Stack[MultiExpansionSequent] // Invariant: the stack only contains valid expansion sequents.
    
    if (prover.isValid(sequent.toDeep)) {
      debug("The starting sequent is tautological.")
      stack.push(sequent) // The sequent under consideration is placed on the stack if it is valid.
      maxRemovedInstance += ((sequent, 0)) // The input sequent is assigned number 0 to denote that no instances at all have been removed from it.
    }
    
    while (!stack.isEmpty) {
      info("Retrieving sequent from stack")
      val (current) = stack.pop() // Topmost element of stack is retrieved. We already know it is tautological; only need to consider its successors.
      debug("Retrieved sequent " + current + ".")
      val n = maxRemovedInstance(current)
      info("Generating successors")
      val newSequents = generateSuccessors(current) // All successor expansion sequents are generated.
      var minimal = true // We assume that the current sequent is minimal unless we find a counterexample.
      
      for (i <- 1 to newSequents.length) { // Iterate over the generated successors
        val s = newSequents(i-1)
        debug("Testing successor " + i)
        if (prover.isValid(s.toDeep)) {
          if (i >= n) // This is the core of the optimization: Avoid pushing sequents on the stack multiple times.
            stack.push(s) // Push valid sequents on the stack
            
          minimal = false // If there is a valid sequent below the current one, it is not minimal.
        }
      }
      
      if (minimal) {
        info("Minimal sequent found.")
        result += current // If the current sequent is minimal, we add it to the results.
      }
    }
    
    result.toSeq
  }
  
  /** Given a MultiExpansionSequent, this generates all sequents obtained by removing one instance from one tree.
    * It also updates the maxRemovedInstance map.
    */
  def generateSuccessors(sequent: MultiExpansionSequent): Seq[MultiExpansionSequent] = sequent match {
    case MultiExpansionSequent(ant, suc) => {
      val newSequents = new ListBuffer[MultiExpansionSequent] //newSequents will be the list of expansion sequents obtained from S by removing one instance from one tree of S.
      var instanceCounter = 0 // Counts the instances of all trees in the sequent.
      
      // Loop over the antecedent.
      for (j <- 1 to ant.length) {
        val (tree, fst, snd) = zipper(ant, j) //We iteratively focus each expansion tree in the antecedent of S.
        val newTrees = generateSuccessorTrees(tree) // We generate all successor trees of the current tree.
        
        if (newTrees.isEmpty) { // This can happen for two reasons: the current tree contains no weak quantifiers or all its weak quantifier nodes have only one instance.
          val newS = MultiExpansionSequent(fst ++ snd, suc) // Since the current tree only consists of one instance, we form a successor sequent simply by deleting it.
          val k = instanceCounter + 1
          
          if (!maxRemovedInstance.contains(newS)) // If there is no entry in maxRemovedInstance for newS, we set it to k.
            maxRemovedInstance += newS -> k
          else if (k > maxRemovedInstance(newS)) // We also update the entry for newS if the current value is higher.
            maxRemovedInstance += newS -> k
          
          newSequents += newS
        }
        else {
          val instanceNumbers = (instanceCounter + 1) to (instanceCounter + newTrees.length)
          
          for ((t,k) <- newTrees zip instanceNumbers) { // k denotes the instance that was removed from tree in order to produce t.
            val newS = MultiExpansionSequent(fst ++ Seq(t) ++snd, suc) // We combine an expansion tree with the rest of the antecedent and the succedent to produce a new expansion sequent.
            
            if (!maxRemovedInstance.contains(newS)) // If there is no entry in maxRemovedInstance for newS, we set it to k.
              maxRemovedInstance += newS -> k
            else if (k > maxRemovedInstance(newS)) // We also update the entry for newS if the current value is higher.
              maxRemovedInstance += newS -> k
            
            newSequents += newS
          }
        }
        instanceCounter += numberOfInstances(tree)
      }
      
      // Loop over the succedent, analogous to the one over the antecedent.
      for (j <- 1 to suc.length) {
        val (tree, fst, snd) = zipper(suc, j)
        val newTrees = generateSuccessorTrees(tree)
        
        if (newTrees.isEmpty) {
          val newS = MultiExpansionSequent(ant, fst ++ snd)
          val k = instanceCounter + 1
          
          if (!maxRemovedInstance.contains(newS))
            maxRemovedInstance += newS -> k
          else if (k > maxRemovedInstance(newS))
            maxRemovedInstance += newS -> k
          
          newSequents += newS
        }
        else {
          val instanceNumbers = (instanceCounter + 1) to (instanceCounter + newTrees.length)
          
          for ((t,k) <- newTrees zip instanceNumbers) {
            val newS = MultiExpansionSequent(ant, fst ++ Seq(t) ++snd)
           
            if (!maxRemovedInstance.contains(newS))
              maxRemovedInstance += newS -> k
            else if (k > maxRemovedInstance(newS))
              maxRemovedInstance += newS -> k
            
            newSequents += newS
          }
        }
        instanceCounter += numberOfInstances(tree)
      }
      
      newSequents.toSeq
    }
  }
  
   /** Given a MultiExpansionTree, this produces all trees obtained by erasing exactly one instance.
    *
    */
  def generateSuccessorTrees(tree: MultiExpansionTree): Seq[MultiExpansionTree] = tree match {
    case Atom(f) => Nil
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
}

object minimalExpansionSequentsSmart {
  def apply(sequent: MultiExpansionSequent, prover: Prover) : Seq[MultiExpansionSequent] = {
    new minimalExpansionSequentsSmart(sequent, prover).compute
  }
  
  def apply(sequent: ExpansionSequent, prover: Prover): Seq[ExpansionSequent] = minimalExpansionSequentsSmart(compressQuantifiers(sequent), prover).map(decompressQuantifiers.apply)
}