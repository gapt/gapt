package at.logic.algorithms.resolution

import collection.immutable
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.robinson.{InitialClause, Factor, Resolution, Variant, Paramodulation, RobinsonResolutionProof}
import at.logic.calculi.resolution.instance.Instance
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.Ti
import at.logic.language.fol.{FOLVar, FOLFormula, FOLExpression, FOLTerm}
import at.logic.algorithms.rewriting.NameReplacement
import at.logic.calculi.resolution.base.Clause
import at.logic.language.lambda.types.Ti
import scala.Some
import at.logic.calculi.lk.base.Sequent
import collection.mutable

/**
 * Eliminates the insantiate rule from a RobinsonResolutionProof
 */
object InstantiateElimination {
  def apply(p:RobinsonResolutionProof) = {
    val ip = imerge(p, emptyProofMap)
    val rp = remove(ip._4, emptyVarSet, emptyProofMap)
    rp._4
  }


  def find_matching[A,B](objects : immutable.List[A], targets : immutable.List[B], matches : (A,B) => Boolean  )
        : immutable.Map[A,B] = NameReplacement.find_matching(objects, targets, matches)

  type OccMap = immutable.Map[FormulaOccurrence, FormulaOccurrence]
  val emptyOccMap = immutable.Map[FormulaOccurrence, FormulaOccurrence]()

  type RenameMap = immutable.Map[Var, Var]
  val emptyRenameMap = immutable.Map[Var, Var]()

  type ProofMap = immutable.Map[RobinsonResolutionProof, (OccMap, VarSet, RobinsonResolutionProof)]
  val emptyProofMap = immutable.Map[RobinsonResolutionProof, (OccMap, VarSet, RobinsonResolutionProof)]()

  type VarSet = immutable.Set[Var]
  val emptyVarSet = immutable.Set[Var]()



  /* for a given substitution s, create a new substitution t from fresh variables. return a pair (r,t) where r
   * is the renaming from old vars to new vars */
  def extract_renaming(s:Substitution[FOLExpression], forbidden: VarSet) : (Substitution[FOLExpression], Substitution[FOLExpression], VarSet) = {
    val vars = s.map.keySet
    val (olds,news)= generate_freshvars(vars, forbidden)

    val olds_new = olds zip news.asInstanceOf[List[FOLExpression]]
    val r = Substitution[FOLExpression](olds_new )
    val t = Substitution[FOLExpression](s.map.map( (el : (Var, FOLExpression)) => (r(el._1.asInstanceOf[FOLVar]).asInstanceOf[Var], el._2) ))

    (r, t, news.toSet)

  }

  /* wrapper around successor(pocc,clause) -- for documentation it's better to ask what the arent clause is */
  def successor(pocc : FormulaOccurrence, parentclause : Clause, clause : Clause) : FormulaOccurrence = {
    require(parentclause.occurrences contains pocc, "Error finding successor, occurrence not present in parentclause")
    successor(pocc, clause)
  }

  /* find successor of occurrence pocc in clause */
  def successor(pocc : FormulaOccurrence, clause : Clause) : FormulaOccurrence = {
    val s = List(pocc)
    clause.occurrences.find( _.ancestors.toList == s ) match {
      case Some(x) => x
      case _ => throw new Exception("Could not find successor of "+pocc.toString+" in "+clause.toString)
    }
  }

  /* find successor of of list of occurrences poccs in clause */
  def successor(poccs : List[FormulaOccurrence], clause : Clause) : FormulaOccurrence = {
    clause.occurrences.find(x =>
      (x.ancestors.toList diff poccs).isEmpty && (poccs diff x.ancestors.toList).isEmpty )
    match {
      case Some(x) => x
      case _ => throw new Exception("Could not find successor of "+poccs.toString+" in "+clause.toString)
    }
  }

  /* if m is a mapping from literals in the parent of original_clause to literals in the parent of new-clause,
   * return a mapping from successor literals to successor literals, works only if the ancestor relation is a
   * bijection (intended use is for the instance rule) */
  def successormap(m : OccMap, original_clause : Clause, new_clause : Clause) : OccMap = {
    val ooccs = original_clause.occurrences
    val noccs = new_clause.occurrences
    m.foldLeft(emptyOccMap)((itmap, pair) => {
      ooccs find (_.ancestors sameElements List(pair._1)) match {
        case Some(poocc) =>
          noccs find (_.ancestors sameElements List(pair._2)) match {
            case Some(pnocc) =>
              itmap +((poocc, pnocc))
            case _ =>
              throw new Exception("Could not find successor"+ pair._2+ " in "+noccs)
          }
        case _ =>
          throw new Exception("Could not find successor"+ pair._1+ " in "+ooccs)
      }
    })

  }

  /* merge instance rules occurring above an inference into its substitution and create a variant to assure there are
    no variable collissions. assumes there are no successive instance rules i.e. imerge must have been called on the
    input proof. */
  def remove(p:RobinsonResolutionProof, forbidden : VarSet, pmap : ProofMap) : (ProofMap, OccMap, VarSet, RobinsonResolutionProof) = {
    if (pmap contains p) return extend_to_quadruple(pmap(p), pmap)
    println("forbidden: "+forbidden)
    println("clause: "+p.root)

    p match {
      case InitialClause(clause) =>
        //no change for initial clause
        extend_pmap(emptyOccMap  ++ (clause.occurrences zip clause.occurrences), forbidden ++ getVars(clause, forbidden), p, pmap )
      case Instance(clause, parent, sub) =>
        val (rpmap, rmap, rforbidden, rparent) = remove(parent, getVars(clause,forbidden), pmap)
        if (rpmap contains p) return extend_to_quadruple(rpmap(p), rpmap)

        val inference = Instance(rparent, sub)
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rmap))

        extend_pmap(nmap, getVars(clause, rforbidden), inference, rpmap)

      case Factor(clause, Instance(iclause, iparent, isub), aux, sub) =>
        val (rpmap, rmap, rforbidden, rparent) = remove(iparent, getVars(clause,forbidden), pmap)
        if (rpmap contains p) return extend_to_quadruple(rpmap(p), rpmap)
        val (renaming, nsub, nvars) = extract_renaming(isub, rforbidden)

        val ivariant = Variant(rparent, renaming)
        def isuccessor(fo: FormulaOccurrence) = successor(rmap(fo), ivariant.root, rparent.root)
        aux match {
          case List(a::as) =>
            val inference = Factor(ivariant, isuccessor(a), as map isuccessor, nsub )
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              rparent.root.occurrences.toList,
              inference.root.occurrences.toList,
              occancmatcher(_,_,rmap))
            extend_pmap(nmap, getVars(ivariant.root, rforbidden ++ nvars), inference , rpmap)

          case List(a::as, b::bs) =>
            val inference = Factor(ivariant, isuccessor(a), as map isuccessor, isuccessor(b), bs map isuccessor,nsub )
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              clause.occurrences.toList,
              inference.root.occurrences.toList,
              occancmatcher(_,_,rmap))
            extend_pmap(nmap, getVars(ivariant.root, rforbidden ++ nvars), inference, rpmap)
          case _ =>
            throw new Exception("Unexpected auxiliary occurrences in handling of Factor rule during instantiation removal!")
        }

      case Factor(clause, parent, aux, sub) =>
        val (rpmap, rmap, rforbidden, rparent) = remove(parent, getVars(clause,forbidden), pmap)
        if (rpmap contains p) return extend_to_quadruple(rpmap(p), rpmap)
        aux match {
          case List(a::as) =>
            val inference = Factor(rparent, rmap(a), as map rmap, sub )
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              rparent.root.occurrences.toList,
              inference.root.occurrences.toList,
              occancmatcher(_,_,rmap))
            extend_pmap(nmap, getVars(clause,rforbidden), inference, rpmap)

          case List(a::as, b::bs) =>
            val inference = Factor(rparent, rmap(a), as map rmap, rmap(b), bs map rmap, sub )
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              clause.occurrences.toList,
              inference.root.occurrences.toList,
              occancmatcher(_,_,rmap))
            extend_pmap(nmap, getVars(clause,rforbidden), inference, rpmap)
          case _ =>
            throw new Exception("Unexpected auxiliary occurrences in handling of Factor rule during instantiation removal!")
        }

      case Resolution(clause, Instance(iclause1, iparent1, isub1), Instance(iclause2, iparent2, isub2), occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(iparent1, getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(iparent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        val (renaming1, nsub1, nvars1) = extract_renaming(isub1, rforbidden)
        val (renaming2, nsub2, nvars2) = extract_renaming(isub2, rforbidden ++ nvars1)

        val vinf1 = Variant(rparent1, renaming1)
        val vinf2 = Variant(rparent2, renaming2)

        val rsmap1 = successormap(rmap1, iclause1 , vinf1.root )
        val rsmap2 = successormap(rmap2, iclause2 , vinf2.root )

        val inference = Resolution(vinf1, vinf2,
          rsmap1(occ1),
          rsmap2(occ2),
          sub compose (nsub1 compose nsub2) )
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rsmap1++rsmap2))

        extend_pmap(nmap, getVars(clause,rforbidden ++ nvars1 ++ nvars2), inference, rpmap2)

      case Resolution(clause, Instance(iclause1, iparent1, isub1), parent2, occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(iparent1, getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(parent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        val (renaming1, nsub1, nvars1) = extract_renaming(isub1, rforbidden)
        val vinf1 = Variant(rparent1, renaming1)
        val rsmap1 = successormap(rmap1, iclause1 , vinf1.root )

        val inference = Resolution(vinf1, rparent2,
          rsmap1(occ1),
          rmap2(occ2),
          sub compose nsub1 )
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rsmap1++rmap2))

        extend_pmap(nmap, getVars(clause,rforbidden ++ nvars1), inference, rpmap2)

      case Resolution(clause, parent1, Instance(iclause2, iparent2, isub2), occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(parent1,  getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(iparent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        val (renaming2, nsub2, nvars2) = extract_renaming(isub2, rforbidden)
        val vinf2 = Variant(rparent2, renaming2)
        val rsmap2 = successormap(rmap2, iclause2 , vinf2.root )

        val inference = Resolution(rparent1, vinf2,
          rmap1(occ1),
          rsmap2(occ2),
          sub compose nsub2 )
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rmap1++rsmap2))

        extend_pmap(nmap, getVars(clause,rforbidden ++ nvars2), inference, rpmap2)

      case Resolution(clause, parent1, parent2, occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(parent1,  getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(parent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        val inference = Resolution(rparent1, rparent2,
          rmap1(occ1),
          rmap2(occ2),
          sub )
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rmap1++rmap2))

        extend_pmap(nmap, getVars(clause,rforbidden), inference, rpmap2)


      case Paramodulation(clause, Instance(iclause1, iparent1, isub1), Instance(iclause2, iparent2, isub2), occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(iparent1,  getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(iparent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        val (renaming1, nsub1, nvars1) = extract_renaming(isub1, rforbidden)
        val (renaming2, nsub2, nvars2) = extract_renaming(isub2, rforbidden ++ nvars1)

        val vinf1 = Variant(rparent1, renaming1)
        val vinf2 = Variant(rparent2, renaming2)

        val rsmap1 = successormap(rmap1, iclause1 , vinf1.root )
        val rsmap2 = successormap(rmap2, iclause2 , vinf2.root )

        val primary = successor(List(occ1,occ2), clause)
        val inference = Paramodulation(vinf1, vinf2,
          rsmap1(occ1),
          rsmap2(occ2),
          primary.formula.asInstanceOf[FOLFormula],
          sub compose (nsub1 compose nsub2) )

        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rsmap1++rsmap2))

        extend_pmap(nmap, getVars(clause,rforbidden ++ nvars1 ++ nvars2), inference, rpmap2)

      case Paramodulation(clause, Instance(iclause1, iparent1, isub1), parent2, occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(iparent1,  getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(parent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        /*
        println("*--*")
        println("iparent1 "+iparent1.root.occurrences)
        println("parent2  "+parent2.root.occurrences)
        println("rparent1 "+rparent1.root.occurrences)
        println("iparent2 "+rparent2.root.occurrences)
          */

        val (renaming1, nsub1, nvars1) = extract_renaming(isub1, rforbidden)
        val vinf1 = Variant(rparent1, renaming1)
        //println("vinf1    "+vinf1.root.occurrences)

        val rsmap1 = successormap(rmap1, iclause1 , vinf1.root )
        //println("rsmap1   "+rsmap1)

        val primary = successor(List(occ1,occ2), clause)
        val inference = Paramodulation(vinf1, rparent2,
          rsmap1(occ1),
          rmap2(occ2),
          primary.formula.asInstanceOf[FOLFormula],
          sub compose nsub1 )
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rsmap1++rmap2))

        extend_pmap(nmap, getVars(clause,rforbidden ++ nvars1), inference, rpmap2)

      case Paramodulation(clause, parent1, Instance(iclause2, iparent2, isub2), occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(parent1,  getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(iparent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        val (renaming2, nsub2, nvars2) = extract_renaming(isub2, rforbidden)
        val vinf2 = Variant(rparent2, renaming2)
        val rsmap2 = successormap(rmap2, iclause2 , vinf2.root )

        val primary = successor(List(occ1,occ2), clause)
        val inference = Paramodulation(rparent1, vinf2,
          rmap1(occ1),
          rsmap2(occ2),
          primary.formula.asInstanceOf[FOLFormula],
          sub compose nsub2 )
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rmap1++rsmap2))

        extend_pmap(nmap, getVars(clause,rforbidden ++ nvars2), inference, rpmap2)

      case Paramodulation(clause, parent1, parent2, occ1, occ2, sub ) =>
        val (rpmap1, rmap1, rforbidden1, rparent1) = remove(parent1,  getVars(clause,forbidden), pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, rforbidden2, rparent2) = remove(parent2, rforbidden1, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val rforbidden = rforbidden1 ++ rforbidden2

        val primary = successor(List(occ1,occ2), clause)
        val inference = Paramodulation(rparent1, rparent2,
          rmap1(occ1),
          rmap2(occ2),
          primary.formula.asInstanceOf[FOLFormula],
          sub)
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_, rmap1++rmap2))

        extend_pmap(nmap, getVars(clause,rforbidden), inference, rpmap2)


      case _ => throw new Exception("Unhandled inference: "+p)



    }
  }




  //true iff the set of ancestors x is translated to the set of ancestors of y
  def occmatcher(x: FormulaOccurrence, y:FormulaOccurrence, occmap : OccMap) : Boolean = {
    val xyanc = x.ancestors.map(occmap)
    val yanc = y.ancestors
    (xyanc diff yanc).isEmpty && (yanc diff xyanc).isEmpty
  }

  //true iff the set of ancestors of the ancestors of x is translated to the set of ancestors of y
  def ancoccmatcher(x: FormulaOccurrence, y:FormulaOccurrence, occmap : OccMap) : Boolean = {
    val xyanc = x.ancestors.map(_.ancestors).flatten
    val yanc = y.ancestors
    (xyanc diff yanc).isEmpty && (yanc diff xyanc).isEmpty
  }
  //true iff the set of ancestors x is translated to the set of ancestors of y
  def occancmatcher(x: FormulaOccurrence, y:FormulaOccurrence, occmap : OccMap) : Boolean = {
    val xyanc = y.ancestors.map(_.ancestors).flatten
    val yanc = x.ancestors
    (xyanc diff yanc).isEmpty && (yanc diff xyanc).isEmpty
  }

  //def extend_to_triple( x : (OccMap, RobinsonResolutionProof), pmap : ProofMap  ) = (pmap, x._1, x._2)
  def extend_to_quadruple( x : (OccMap, VarSet, RobinsonResolutionProof), pmap : ProofMap  ) = (pmap, x._1, x._2, x._3)
  def extend_pmap( o : OccMap, f:VarSet, p: RobinsonResolutionProof, pmap : ProofMap  )  :
   (ProofMap, OccMap, VarSet, RobinsonResolutionProof) = {
    /*
    println("***")
    println("returning occmap: "+o)
    println("literals: "+p.root.occurrences)
    println("proof: "+p)
    println("proofmap: "+pmap)
    println()
     */
    (pmap + ((p,(o,f,p))), o, f, p )
  }

  //def extend_pmap2( o : OccMap,  p: RobinsonResolutionProof, pmap : ProofMap  ) = {
  //  (pmap + ((p,(o,p))), o, p )
  //}


  def imerge(p : RobinsonResolutionProof, pmap : ProofMap) : (ProofMap, OccMap, VarSet, RobinsonResolutionProof) = {
     p match {
      case InitialClause(clause) =>
        if (pmap contains p) return extend_to_quadruple(pmap(p), pmap)
        //no change for initial clause
        extend_pmap(emptyOccMap  ++ (clause.occurrences zip clause.occurrences), emptyVarSet, p, pmap )

      case Instance(clause, parent, sub) =>
        val (rpmap, rmap, f, rparent) = imerge(parent, pmap)
        if (rpmap contains p) return extend_to_quadruple(rpmap(p), rpmap)

        if (sub.isIdentity) {
          val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
            clause.occurrences.toList,
            rparent.root.occurrences.toList,
            _.formula syntaxEquals _.formula)

          return (rpmap + ((p, (nmap, f, rparent))), nmap, f, rparent)
        }

        rparent match {
          //merging
          case Instance(rpclause, rpparent, rpsub) =>

            val inference = Instance(rpparent, sub compose rpsub)
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              clause.occurrences.toList,
              inference.root.occurrences.toList,
              _.formula syntaxEquals _.formula)

            extend_pmap(nmap, emptyVarSet, inference, pmap)

          case _ =>
            //don't do anything
            val inference = Instance(rparent, sub)
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              clause.occurrences.toList,
              inference.root.occurrences.toList,
              _.formula syntaxEquals _.formula)

            extend_pmap(nmap, emptyVarSet, inference, pmap)

        }

      case Factor(clause, parent, occs, sub) =>
        val (rpmap, rmap, _, rparent) = imerge(parent, pmap)
        if (rpmap contains p) return extend_to_quadruple(rpmap(p), rpmap)
        occs.length match {
          case 1 =>
            val inference = Factor(rparent, occs(0)(0), occs(0).tail, sub)
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              clause.occurrences.toList,
              inference.root.occurrences.toList,
              occmatcher(_,_,rmap))
            extend_pmap(nmap, emptyVarSet, inference, pmap)

          case 2 =>
            val inference = Factor(rparent, occs(0)(0), occs(0).tail, occs(1)(0), occs(1).tail, sub)
            val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
              clause.occurrences.toList,
              inference.root.occurrences.toList,
              occmatcher(_,_,rmap))
            extend_pmap(nmap, emptyVarSet, inference, pmap)

          case _ => throw new Exception("Unexpected auxiliary occurrences in handling of Factor rule during instantiation merge!")
        }

      case Variant(clause, parent, sub) =>
        val (rpmap, rmap, _, rparent) = imerge(parent, pmap)
        if (rpmap contains p) return extend_to_quadruple(rpmap(p), rpmap)
        val inference = Variant(rparent, sub)
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_,rmap))
        extend_pmap(nmap, emptyVarSet, inference, pmap)

      case Resolution(clause, parent1, parent2, occ1, occ2, sub) =>
        val (rpmap1, rmap1, _, rparent1) = imerge(parent1, pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, _, rparent2) = imerge(parent2, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val inference = Resolution(rparent1, rparent2, rmap1(occ1), rmap2(occ2), sub)
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_,rmap1 ++ rmap2))
        extend_pmap(nmap, emptyVarSet, inference, pmap)

      case Paramodulation(clause, parent1, parent2, occ1, occ2, sub) =>
        val (rpmap1, rmap1, _, rparent1) = imerge(parent1, pmap)
        if (rpmap1 contains p) return extend_to_quadruple(rpmap1(p), rpmap1)
        val (rpmap2, rmap2, _, rparent2) = imerge(parent2, rpmap1)
        if (rpmap2 contains p) return extend_to_quadruple(rpmap2(p), rpmap2)

        val primary_candidates = clause.occurrences.filter((fo:FormulaOccurrence) => {fo.ancestors.size == 2 && fo.ancestors.contains(occ1) && fo.ancestors.contains(occ2) })
        if (primary_candidates.isEmpty) throw new Exception("Could not find primary formula during handling of Paramodulation in instantiation merge!")
        val primary = primary_candidates.head.formula.asInstanceOf[FOLFormula]

        val inference = Paramodulation(rparent1, rparent2, rmap1(occ1), rmap2(occ2), primary, sub)
        val nmap = find_matching[FormulaOccurrence, FormulaOccurrence](
          clause.occurrences.toList,
          inference.root.occurrences.toList,
          occmatcher(_,_,rmap1 ++ rmap2))
        extend_pmap(nmap, emptyVarSet, inference, pmap)

     }
  }

  private var generated = immutable.Set[Var]()

  /* for each element v in vl generate a fresh variable f, return a list of pairs (v,f) */
  def generate_freshvars(vl:VarSet, forbidden : VarSet) : (List[Var], List[Var]) = {
    val (olds,news) = vl.foldLeft((List[Var](), forbidden.toList ++ generated))((xs:(List[Var], List[Var]), v:Var) => {
      val fresh = freshVar(Ti(), xs._2.toSet, (x:Int) => "x_{"+x.toString+"}" , v.factory )
      //require(! (generated contains fresh), "Error in creating blacklist!")
      generated = generated+fresh
      (v::xs._1, fresh :: xs._2)
     } )
    (olds,news)
  }

  def commonvars[T <: LambdaExpression](s1:Substitution[T], s2: Substitution[T]) : immutable.Set[Var] = {
    val k1 = s1.map.keySet
    val k2 = s2.map.keySet
    k1.filter(k2.contains) //++ k2.filter(k1.contains)
  }

  def getVars(exp : LambdaExpression, vs : VarSet) : VarSet = exp match {
    case Var(_,_) => vs + exp.asInstanceOf[Var]
    case App(s,t) => getVars(s, getVars(t,vs))
    case Abs(x,s) => getVars(s, vs+x)
  }

  def getVars(s:Sequent, forbidden : VarSet) : VarSet =
    s.occurrences.foldLeft(forbidden)((s: VarSet, fo: FormulaOccurrence) => s ++ getVars(fo.formula,s))

  def getVars(ss: Seq[Sequent], forbidden :VarSet) : VarSet = ss.foldLeft(forbidden)((set:VarSet, s:Sequent ) => getVars(s, set))

}
