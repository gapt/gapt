package at.logic.algorithms.expansionTrees

import at.logic.provers.Prover
import scala.collection.mutable.{Stack, HashSet, ListBuffer}
import at.logic.calculi.expansionTrees.multi._

// object minimalExpansionSequentsSmart {
//   type NumberedExpansionSequent = (Seq[(MultiExpansionTree, Int)], Seq[(MultiExpansionTree, Int)])
//   
// /** Given a MultiExpansionSequent S, returns the list of MultiExpansionSequents below or equal to S that still have tautological deep sequents.
// 
// */
// //   def applyRecursive(sequent: MultiExpansionSequent, prover: Prover9Prover) : List[MultiExpansionSequent] = {
// //     val deepSequent = sequent.toDeepSequent
// //     if (prover.isValid(deepSequent)) { //If the deep sequent of S is valid, there might be minimal sequents below S.
// //       //println("Deep sequent " ++ deepSequent.toString ++ " is valid.")
// //       val newSequents = generateSuccessors(sequent)
// //       //println("New expansion sequents generated: " ++ newSequents.toString)
// //       val minimals = newSequents.flatMap(this.apply(_,prover)) //We recursively call this algorithm in order to find the minimal elements below the successors of S.
// //           
// //       if (minimals.isEmpty)
// //         List(sequent) //If there are none, then S itself is minimal.
// //       else
// //         minimals //Otherwise we simply return the minimal elements below S.
// //     }
// //     else //If the deep sequent of S is not valid, there are certainly no minimal elements below or equal to S.
// //       Nil
// //   }
//   def apply(sequent: MultiExpansionSequent, prover: Prover) : List[MultiExpansionSequent] = applyIterative(sequent, prover)
//   
//   def applyIterative(sequent: MultiExpansionSequent, prover: Prover) : List[MultiExpansionSequent] = {
//     val result= new HashSet[MultiExpansionSequent]
//     val stack = new Stack[NumberedExpansionSequent]
//     val sequentNum = (sequent.antecedent.map(x => (x,1)), sequent.succedent.map(x => (x,1)))
//     
//     if (prover.isValid(sequent.toDeep))
//       stack.push(sequentNum)
//     
//     while (!stack.isEmpty) {
//       var currentNum = stack.pop()
//       var current = MultiExpansionSequent(currentNum._1.map(x => x._1),currentNum._2.map(x => x._1))
//       println("Retrieved sequent " ++current.toString++ " from Stack.")
//       var newSequents = generateSuccessors(currentNum)
//       println(newSequents.length.toString ++ " successors generated.")
//       var minimal = true
//       
//       for (sNum <- newSequents) {
//         val s = MultiExpansionSequent(sNum._1.map(x => x._1),sNum._2.map(x => x._1))
//         println("Considering sequent " ++s.toString++ "...")
//         if (prover.isValid(s.toDeep)) {
//           stack.push(sNum)
//           minimal = false
//           println("Sequent is tautological.")
//         }
//         else
//           println("Sequent is not tautological.")
//       }
//       
//       if (minimal)
//         result += current
//     }
//     
//     result.toList
//   }
//   
// //   def generateSuccessors(sequent: MultiExpansionSequent): List[MultiExpansionSequent] = sequent.toTuple match {
// //     case (ant, suc) => {
// //       var newSequents : List[MultiExpansionSequent] = Nil //newSequents will be the list of expansion sequents obtained from S by removing one instance from one tree of S.
// //       for (j <- 1 to ant.length) {
// //         val (tree, fst, snd) = zipper(ant.toList, j) //We iteratively focus each expansion tree in the antecedent of S.
// //         //println("Expansion tree " ++ tree.toString ++" [" ++ j.toString++"/"++ant.length.toString++"] in focus.")
// //         tree match {
// //           case mWeakQuantifier(f, inst) => {
// //             if (inst.length > 1) {  
// //               //println("Current instances: " ++ inst.toString)
// //               val instances = listComplements(inst.toList) //These two lines generate all expansion trees that result from removing an instance from tree.
// //               //println("New instances: " ++ instances.toString)
// //               val newTrees = instances.map(i => mWeakQuantifier(f,i))
// //               //println("New trees: " ++ newTrees.toString)
// //               newSequents = newSequents ++ newTrees.map(t => MultiExpansionSequent(fst ++ List(t) ++ snd, suc))
// //               //println("New sequents: " ++ newSequents.toString)
// //             }
// //           }
// //               
// // //               case mAtom(f) => {newSequents = newSequents ++ List(MultiExpansionSequent(fst ++ snd, suc))
// // //               println("New sequents: " ++ newSequents.toString)}
// //           case _ => {}
// //         }
// //       }
// //           
// //       for (j <- 1 to suc.length) { //This for loop is analogous to the one for the antecedent.
// //         val (tree, fst, snd) = zipper(suc.toList, j)
// //         //println("Expansion tree " ++ tree.toString ++" [" ++ j.toString++"/"++suc.length.toString++"] in focus.")
// //         tree match {
// //           case mWeakQuantifier(f, inst) => {
// //             if (inst.length > 1) {
// //               //println("Current instances: " ++ inst.toString)
// //               val instances = listComplements(inst.toList)
// //               //println("New instances: " ++ instances.toString)
// //               val newTrees = instances.map(i => mWeakQuantifier(f,i))
// //               //println("New trees: " ++ newTrees.toString)
// //               newSequents = newSequents ++ newTrees.map(t => MultiExpansionSequent(ant, fst ++ List(t) ++ snd))
// //               //println("New sequents: " ++ newSequents.toString)
// //             }
// //           }
// //               
// // //               case mAtom(f) => {newSequents = newSequents ++ List(MultiExpansionSequent(ant, fst ++ snd))
// // //               println("New sequents: " ++ newSequents.toString)}
// //           case _ => {}
// //         }
// //       }
// //           
// //       newSequents
// //     }
// //   }
//   
//   def generateSuccessors(sequent: NumberedExpansionSequent): List[NumberedExpansionSequent] = sequent match {
//     case (ant, suc) => {
//       var newSequents : List[NumberedExpansionSequent] = Nil //newSequents will be the list of expansion sequents obtained from S by removing one instance from one tree of S.
//       for (j <- 1 to ant.length) {
//         val ((tree,n), fst, snd) = zipper(ant.toList, j) //We iteratively focus each expansion tree in the antecedent of S.
//         //println("Expansion tree " ++ tree.toString ++" [" ++ j.toString++"/"++ant.length.toString++"] in focus.")
//         tree match {
//           case WeakQuantifier(f, inst) => {
//             if (inst.length > 1) {  
//               //println("Current instances: " ++ inst.toString)
//               val instances = listComplements(inst.toList,n) //These two lines generate all expansion trees that result from removing an instance from tree.
//               //println("New instances: " ++ instances.toString)
//               val newTrees = instances.map(i => (WeakQuantifier(f,i._1), i._2))
//               //println("New trees: " ++ newTrees.toString)
//               newSequents = newSequents ++ newTrees.map(t => (fst ++ List(t) ++ snd, suc))
//               //println("New sequents: " ++ newSequents.toString)
//             }
//           }
//               
// //               case mAtom(f) => {newSequents = newSequents ++ List(MultiExpansionSequent(fst ++ snd, suc))
// //               println("New sequents: " ++ newSequents.toString)}
//           case _ =>
//         }
//       }
//           
//       for (j <- 1 to suc.length) { //This for loop is analogous to the one for the antecedent.
//         val ((tree, n), fst, snd) = zipper(suc.toList, j)
//         //println("Expansion tree " ++ tree.toString ++" [" ++ j.toString++"/"++suc.length.toString++"] in focus.")
//         tree match {
//           case WeakQuantifier(f, inst) => {
//             if (inst.length > 1) {
//               //println("Current instances: " ++ inst.toString)
//               val instances = listComplements(inst.toList, n)
//               //println("New instances: " ++ instances.toString)
//               val newTrees = instances.map(i => (WeakQuantifier(f,i._1), i._2))
//               //println("New trees: " ++ newTrees.toString)
//               newSequents = newSequents ++ newTrees.map(t => (ant, fst ++ List(t) ++ snd))
//               //println("New sequents: " ++ newSequents.toString)
//             }
//           }
//               
// //               case mAtom(f) => {newSequents = newSequents ++ List(MultiExpansionSequent(ant, fst ++ snd))
// //               println("New sequents: " ++ newSequents.toString)}
//           case _ =>
//         }
//       }
//           
//       newSequents
//     }
//   }
//   
// /** Given a list xs, returns a list of copies of xs without the first, second, ... element.
// 
// */
//   private def listComplements[T](xs: List[T]) : List[(List[T], Int)] = xs match {
//     case Nil     => Nil
//     case List(y) => List((Nil,1))
//     case y :: ys => (ys,1) :: listComplements(ys).map(p => (y :: p._1, p._2 + 1))
//   }
//   
//   private def listComplements[T](xs: List[T], n: Int) : List[(List[T], Int)] = {
//     val (fst, snd) = xs splitAt (n-1)
//     listComplements(snd).map(p => (fst ++ p._1, p._2 +n-1))
//   }
//   
// /** Splits a list into (nth element, elements 1,..,(n-1), elements (n+1),..,end)
// 
// */
//   private def zipper[T](xs: List[T], n: Int) : (T, List[T], List[T]) = xs match {
//     case Nil     => throw new IllegalArgumentException
//     case y :: ys => {
//       if (n == 1)
//         (y, Nil, ys)
//       else {
//         val (z, fst, snd) = zipper(ys, n-1)
//         (z, y :: fst, snd)
//       }
//     }
//   }
// }

object minimalExpansionSequents {
  
  def apply(sequent: MultiExpansionSequent, prover: Prover) : List[MultiExpansionSequent] = {
    val result= new HashSet[MultiExpansionSequent] // The list of minimal expansion proofs will be constructed iteratively.
    val stack = new Stack[MultiExpansionSequent] // Invariant: the stack only contains tautological expansion sequents.
    
    if (prover.isValid(sequent.toDeep))
      stack.push(sequent) // The sequent under consideration is placed on the stack if it is tautological.
    
    while (!stack.isEmpty) {
      var current = stack.pop() // Topmost element of stack is retrieved. We already know it is tautological; only need to consider its successors.
      //println("Retrieved sequent " ++current.toString++ " from Stack.")
      var newSequents = generateSuccessors(current) // All successor expansion sequents are generated.
      //println(newSequents.length.toString ++ " successors generated.")
      var minimal = true // We assume that the current sequent is minimal unless we prove otherwise.
      
      for (s <- newSequents) { // Iterate over the generated successors
        //println("Considering sequent " ++s.toString++ "...")
        if (prover.isValid(s.toDeep)) {
          stack.push(s) // Push valid sequents on the stack
          minimal = false // If there is a valid sequent below the current one, it is not minimal.
          //println("Sequent is tautological.")
        }
        //else
          //println("Sequent is not tautological.")
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
        //println("Expansion tree " ++ tree.toString ++" [" ++ j.toString++"/"++ant.length.toString++"] in focus.")
        tree match {
          case WeakQuantifier(f, inst) => {
            if (inst.length > 1) {  
              //println("Current instances: " ++ inst.toString)
              val instances = listComplements(inst.toList) //These two lines generate all expansion trees that result from removing an instance from tree.
              //println("New instances: " ++ instances.toString)
              val newTrees = instances.map(i => WeakQuantifier(f,i))
              //println("New trees: " ++ newTrees.toString)
              newSequents ++= newTrees.map(t => MultiExpansionSequent(fst ++ List(t) ++ snd, suc))
              //println("New sequents: " ++ newSequents.toString)
            }
          }
              
//               case mAtom(f) => {newSequents = newSequents ++ List(MultiExpansionSequent(fst ++ snd, suc))
//               println("New sequents: " ++ newSequents.toString)}
          case _ =>
        }
      }
          
      for (j <- 1 to suc.length) { //This for loop is analogous to the one for the antecedent.
        val (tree, fst, snd) = zipper(suc.toList, j)
        //println("Expansion tree " ++ tree.toString ++" [" ++ j.toString++"/"++suc.length.toString++"] in focus.")
        tree match {
          case WeakQuantifier(f, inst) => {
            if (inst.length > 1) {
              //println("Current instances: " ++ inst.toString)
              val instances = listComplements(inst.toList)
              //println("New instances: " ++ instances.toString)
              val newTrees = instances.map(i => WeakQuantifier(f,i))
              //println("New trees: " ++ newTrees.toString)
              newSequents ++= newTrees.map(t => MultiExpansionSequent(ant, fst ++ List(t) ++ snd))
              //println("New sequents: " ++ newSequents.toString)
            }
          }
              
//               case mAtom(f) => {newSequents = newSequents ++ List(MultiExpansionSequent(ant, fst ++ snd))
//               println("New sequents: " ++ newSequents.toString)}
          case _ =>
        }
      }
          
      newSequents.toList
    }
  }
  

/** Given a list xs, returns a list of copies of xs without the first, second, ... element.

*/
  private def listComplements[T](xs: List[T]) : List[List[T]] = xs match {
    case Nil     => Nil
    case y :: ys => ys :: listComplements(ys).map(zs => y :: zs)
  }
  
  private def listComplements[T](xs: List[T], n: Int) : List[List[T]] = {
    val (fst, snd) = xs splitAt (n-1)
    listComplements(snd).map(zs => fst ++ zs)
  }
  
/** Splits a list into (nth element, elements 1,..,(n-1), elements (n+1),..,end)

*/
  private def zipper[T](xs: List[T], n: Int) : (T, List[T], List[T]) = xs match {
    case Nil     => throw new IllegalArgumentException
    case y :: ys => {
      if (n == 1)
        (y, Nil, ys)
      else {
        val (z, fst, snd) = zipper(ys, n-1)
        (z, y :: fst, snd)
      }
    }
  }
  
}