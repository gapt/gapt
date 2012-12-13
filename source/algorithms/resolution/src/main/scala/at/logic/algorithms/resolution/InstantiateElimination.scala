package at.logic.algorithms.resolution

import collection.immutable
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.robinson.{InitialClause, Factor, Resolution, Variant, Paramodulation, RobinsonResolutionProof}
import at.logic.calculi.resolution.instance.Instance
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{freshVar, Var, LambdaExpression}
import at.logic.language.lambda.types.Ti
import at.logic.language.fol.{FOLFormula, FOLExpression, FOLTerm}
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

  type ProofMap = immutable.Map[RobinsonResolutionProof, (OccMap, RobinsonResolutionProof)]
  val emptyProofMap = immutable.Map[RobinsonResolutionProof, (OccMap, RobinsonResolutionProof)]()


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
    val xyanc = x.ancestors.map(_.ancestors).flatten
    val yanc = y.ancestors
    (xyanc diff yanc).isEmpty && (yanc diff xyanc).isEmpty
  }

  def extend_to_triple( x : (OccMap,RobinsonResolutionProof), pmap : ProofMap  ) = (pmap, x._1, x._2)
  def extend_pmap( o : OccMap, p: RobinsonResolutionProof, pmap : ProofMap  ) = (pmap + ((p,(o,p))), o, p )

  def imerge(p : RobinsonResolutionProof, pmap : ProofMap) : (ProofMap, OccMap, RobinsonResolutionProof) = {
     p match {
      case InitialClause(clause) =>

        //no change for initial clause
        extend_pmap(emptyOccMap  ++ (clause.occurrences zip clause.occurrences), p, pmap )

      case Instance(clause, parent, sub) =>
        val (rpmap, rmap, rparent) = imerge(parent, pmap)
        if (rpmap contains p) return extend_to_triple(rpmap(p), rpmap)

        rparent match {
          //merging
          case Instance(rpclause, rpparent, rpsub) =>
            /*
            val clashvars = commonvars(sub, rpsub)
            val (oldvars, newvars1) = generate_freshvars(sub.map.keySet -- clashvars)

            val renaming1 = emptyRenameMap ++ (oldvars zip newvars1)
            val variantsub = Substitution[FOLExpression](renaming1.asInstanceOf[immutable.Map[Var, FOLExpression]])
            //          val renaming2 = emptyRenameMap ++ (oldvars zip newvars2)
            val nsub1 = Substitution[FOLExpression]( rpsub.map.toList map ((x:(Var, FOLExpression)) => (renaming1(x._1), x._2) ) )
            //          val nsub2 = Substitution[FOLExpression]( rpsub.map.toList map ((x:(Var, FOLExpression)) => (renaming1(x._1), x._2) ) )
            */


            val inference = Instance(rpparent, sub compose rpsub)
            val nmap = find_matching( rpparent.root.occurrences.toList, inference.root.occurrences.toList, (x:FormulaOccurrence, y:FormulaOccurrence) => x.formula syntaxEquals y.formula)

            extend_pmap(nmap, inference, pmap)

          case _ =>
            //don't do anything
            val inference = Instance(rparent, sub)
            val nmap = find_matching( parent.root.occurrences.toList, inference.root.occurrences.toList, (x:FormulaOccurrence, y:FormulaOccurrence) => x.formula syntaxEquals y.formula)
            extend_pmap(nmap, inference, pmap)

        }

      case Factor(clause, parent, occs, sub) =>
        val (rpmap, rmap, rparent) = imerge(parent, pmap)
        if (rpmap contains p) return extend_to_triple(rpmap(p), rpmap)
        occs.length match {
          case 1 =>
            val inference = Factor(rparent, occs(0)(0), occs(0).tail, sub)
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence]( parent.root.occurrences.toList, inference.root.occurrences.toList, occmatcher(_,_,rmap))
            extend_pmap(nmap, inference, pmap)

          case 2 =>
            val inference = Factor(rparent, occs(0)(0), occs(0).tail, occs(1)(0), occs(1).tail, sub)
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence]( parent.root.occurrences.toList, inference.root.occurrences.toList,  occmatcher(_,_,rmap))
            extend_pmap(nmap, inference, pmap)

          case _ => throw new Exception("Unexpected auxiliary occurrences in handling of Factor rule during instantiation merge!")
        }

      case Variant(clause, parent, sub) =>
        val (rpmap, rmap, rparent) = imerge(parent, pmap)
        if (rpmap contains p) return extend_to_triple(rpmap(p), rpmap)
        val inference = Variant(rparent, sub)
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence]( parent.root.occurrences.toList, inference.root.occurrences.toList, occmatcher(_,_,rmap))
        extend_pmap(nmap, inference, pmap)

      case Resolution(clause, parent1, parent2, occ1, occ2, sub) =>
        val (rpmap1, rmap1, rparent1) = imerge(parent1, pmap)
        if (rpmap1 contains p) return extend_to_triple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rparent2) = imerge(parent2, rpmap1)
        if (rpmap2 contains p) return extend_to_triple(rpmap2(p), rpmap2)

        val inference = Resolution(rparent1, rparent2, rmap1(occ1), rmap2(occ2), sub)
        val poccs =  parent1.root.occurrences ++  parent2.root.occurrences
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence]( poccs.toList, inference.root.occurrences.toList, occmatcher(_,_,rmap2))
        extend_pmap(nmap, inference, pmap)

      case Paramodulation(clause, parent1, parent2, occ1, occ2, sub) =>
        val (rpmap1, rmap1, rparent1) = imerge(parent1, pmap)
        if (rpmap1 contains p) return extend_to_triple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rparent2) = imerge(parent2, rpmap1)
        if (rpmap2 contains p) return extend_to_triple(rpmap2(p), rpmap2)

        val primary_candidates = clause.occurrences.filter((fo:FormulaOccurrence) => {fo.ancestors.size == 2 && fo.ancestors.contains(occ1) && fo.ancestors.contains(occ2) })
        if (primary_candidates.isEmpty) throw new Exception("Could not find primary formula during handling of Paramodulation in instantiation merge!")
        val primary = primary_candidates.head.formula.asInstanceOf[FOLFormula]

        val inference = Paramodulation(rparent1, rparent2, rmap1(occ1), rmap2(occ2), primary, sub)
        val poccs =  parent1.root.occurrences ++  parent2.root.occurrences
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence]( poccs.toList, inference.root.occurrences.toList, occmatcher(_,_,rmap2))
        extend_pmap(nmap, inference, pmap)




     }
  }

  def generate_freshvars(vl:Set[Var]) = vl.foldLeft((List[Var](), List[Var]()))((xs:(List[Var], List[Var]), v:Var) =>
    (v::xs._1, freshVar(Ti(), xs._2.toSet, v.factory ) :: xs._2)
  )

  def commonvars[T <: LambdaExpression](s1:Substitution[T], s2: Substitution[T]) : immutable.Set[Var] = {
    val k1 = s1.map.keySet
    val k2 = s2.map.keySet
    k1.filter(k2.contains) //++ k2.filter(k1.contains)
  }


}
