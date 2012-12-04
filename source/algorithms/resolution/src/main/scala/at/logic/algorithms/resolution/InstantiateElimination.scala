package at.logic.algorithms.resolution

import collection.immutable
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.robinson.{InitialClause, Factor, Resolution, Variant, Paramodulation, RobinsonResolutionProof}
import at.logic.calculi.resolution.instance.Instance
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{freshVar, Var, LambdaExpression}
import at.logic.language.lambda.types.Ti
import at.logic.language.fol.{FOLExpression, FOLTerm}
import at.logic.algorithms.rewriting.NameReplacement

/**
 * Eliminates the insantiate rule from a RobinsonResolutionProof
 */
object InstantiateElimination {
  def find_matching[A,B](objects : immutable.List[A], targets : immutable.List[B], matches : (A,B) => Boolean  )
        : immutable.Map[A,B] = NameReplacement.find_matching(objects, targets, matches)

  type OccMap = immutable.Map[FormulaOccurrence, FormulaOccurrence]
  val emptyOccMap = immutable.Map[FormulaOccurrence, FormulaOccurrence]()

  type RenameMap = immutable.Map[Var, Var]
  val emptyRenameMap = immutable.Map[Var, Var]()


  def remove(p:RobinsonResolutionProof) : (OccMap, RobinsonResolutionProof) = p match {
    case InitialClause(clause) =>
      //no change for initial clause
      (emptyOccMap  ++ (clause.occurrences zip clause.occurrences), p )
    case Instance(clause, parent, sub) =>
      val (rmap, rparent) = remove(parent)
      (rmap,rparent) //TODO fill in
  }

  //true iff the set of ancestors x is translated to the set of ancestors of y
  def occmatcher(x: FormulaOccurrence, y:FormulaOccurrence, occmap : OccMap) : Boolean = {
    val xyanc = x.ancestors.map(occmap)
    val yanc = y.ancestors
    (xyanc diff yanc).isEmpty && (yanc diff xyanc).isEmpty
  }

  //true iff the set of ancestors x is translated to the set of ancestors of y
  def ancoccmatcher(x: FormulaOccurrence, y:FormulaOccurrence, occmap : OccMap) : Boolean = {
    val xyanc = x.ancestors.map(occmap)
    val yanc = y.ancestors
    (xyanc diff yanc).isEmpty && (yanc diff xyanc).isEmpty
  }

  def imerge(p : RobinsonResolutionProof) : (OccMap, RobinsonResolutionProof) = p match {
    case InitialClause(clause) =>
      //no change for initial clause
      (emptyOccMap  ++ (clause.occurrences zip clause.occurrences), p )
    case Instance(clause, parent, sub) =>
      val (rmap, rparent) = imerge(parent)
      rparent match {
        case Instance(rpclause, rpparent, rpsub) =>
          val clashvars = commonvars(sub, rpsub)
          val (oldvars, newvars) = (clashvars.foldLeft((List[Var](), List[Var]()))((xs:(List[Var], List[Var]), v:Var) => {
                    val (ovs, nvs) = xs
                    (v::ovs, freshVar(Ti(), nvs.toSet, v.factory ) :: nvs)
                  }))

          val renaming = emptyRenameMap ++ (oldvars zip newvars)
          val nsub1 = Substitution[FOLExpression]( rpsub.map.toList map ((x:(Var, FOLExpression)) => (renaming(x._1), x._2) ) )
          val inference = Instance(rpparent, nsub1)
          val nmap = find_matching( rpparent.root.occurrences.toList, inference.root.occurrences.toList, (x:FormulaOccurrence,y:FormulaOccurrence) => true  )
          //TODO: finish

          (rmap,inference)
      }

  }


  def commonvars[T <: LambdaExpression](s1:Substitution[T], s2: Substitution[T]) : immutable.Set[Var] = {
    val k1 = s1.map.keySet
    val k2 = s2.map.keySet
    k1.filter(k2.contains) //++ k2.filter(k1.contains)
  }

}
