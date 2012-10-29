package at.logic.provers.prover9.ivy.conversion
import at.logic.provers.prover9.ivy.{InitialClause => IInitialClause, Instantiate => IInstantiate, Resolution => IResolution,
                                 Paramodulation => IParamodulation, IvyResolutionProof, Flip, Propositional => IPropositional}
import at.logic.calculi.resolution.robinson.{InitialClause => RInitialClause, Resolution => RResolution, Factor => RFactor,
  Variant => RVariant, Paramodulation => RParamodulation, RobinsonResolutionProof}
import at.logic.language.fol.{FOLExpression, FOLTerm, FOLFormula}
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, VariantGenerator, Var}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.resolution.instance.{Instance => RInstantiate}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.base.Clause
import collection.immutable

/**
 * Converts Ivy Proofs into Robinson Resolution Proofs
 */
object IvyToRobinson {
  val generator : VariantGenerator = new VariantGenerator( new {var c = 10000; def nextId = {c = c+1; c}} , "iv" )
  type ProofMap = immutable.Map[String, RobinsonResolutionProof]

  def apply(iproof : IvyResolutionProof) : RobinsonResolutionProof = apply(iproof, immutable.Map[String, RobinsonResolutionProof]())._1
  def apply(iproof : IvyResolutionProof, map :  ProofMap) : (RobinsonResolutionProof, ProofMap) = iproof match {
    case IInitialClause(id, exp, clause) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          val rproof = RInitialClause(clause.negative map (_.formula.asInstanceOf[FOLFormula]), clause.positive map (_.formula.asInstanceOf[FOLFormula]))
          (rproof, map + ((id,rproof)))
      }

    case IInstantiate(id, exp, sub, clause, parent) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          val (pproof, parentmap) = IvyToRobinson(parent, map)
          val rproof = RInstantiate(pproof, sub.asInstanceOf[Substitution[FOLExpression]])
          (rproof, parentmap + ((id, rproof)))
      }
    case IResolution(id, exp, lit1, lit2, clause, parent1, parent2) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          val (rparent1, parentmap1) = IvyToRobinson(parent1, map)
          val (rparent2, parentmap2) = IvyToRobinson(parent2, parentmap1)
          val (polarity1, _, index1) = getIndex(lit1, parent1.vertex, rparent1.vertex)
          val (polarity2, _, index2) = getIndex(lit2, parent2.vertex, rparent2.vertex)

          (polarity1, polarity2) match {
            case (true,false) =>
              require(rparent1.vertex.succedent(index1).formula == lit1.formula, "Left parent literal must be correctly found!")
              require(rparent2.vertex.antecedent(index2).formula == lit2.formula,
                "Right parent literal "+lit2+" at pos "+ index2 +" must be correctly found!" + rparent2.vertex)

              val rproof = RResolution(rparent1, rparent2, rparent1.vertex.succedent(index1), rparent2.vertex.antecedent(index2), Substitution[FOLExpression]())
              (rproof, parentmap2 + ((id, rproof)))
            case (false,true) =>
              require(rparent1.vertex.antecedent(index1).formula == lit1.formula, "Left parent literal must be correctly found!")
              require(rparent2.vertex.succedent(index2).formula == lit2.formula,
                "Right parent literal "+lit2+" at pos "+ index2 +" must be correctly found!" + rparent2.vertex)

              val rproof = RResolution(rparent2, rparent1, rparent2.vertex.succedent(index2), rparent1.vertex.antecedent(index1), Substitution[FOLExpression]())
              (rproof, parentmap2 + ((id, rproof)))
            case _ => throw new Exception("Error in processing ivy proof: resolved literals "+lit1+" and "+lit2+
                                          " do not have different polarity!")
          }
      }

    case IPropositional(id, exp, clause, parent) =>
      def remove_first(el:FormulaOccurrence, l:immutable.Seq[FormulaOccurrence])
         : (FormulaOccurrence, immutable.List[FormulaOccurrence]) = l.toList match {
        case x::Nil =>
          if (x.formula == el.formula)
            (x, Nil)
          else {
            throw new Exception("Error: element "+el+" to remove not contained in list!")
          }
        case x::xs =>
          if (x.formula == el.formula)
            (x, xs)
          else {
            val (removed, rest) = remove_first(el,xs)
            (removed, x::rest)
          }
        case Nil => throw new Exception("Error: want to remove element "+el+" from an empty list!")
      }

      def remove_firsts(fs:immutable.Seq[FormulaOccurrence], l:immutable.Seq[FormulaOccurrence]) :
       (immutable.List[FormulaOccurrence], immutable.Seq[FormulaOccurrence]) = {
        if (fs.isEmpty) { (Nil, l) } else {
            val (el, rest) = remove_first(fs.head,l)
            val (r1,r2) = remove_firsts(fs.tail, rest)
            (el::r1, r2)
        }
      }

      def connect(ivy : immutable.List[FormulaOccurrence], robinson : immutable.Seq[FormulaOccurrence])
           : immutable.List[FormulaOccurrence] = ivy match {
        case x::xs =>
          val (rancs, rem) = remove_firsts(x.ancestors.toList, robinson)
          new FormulaOccurrence(x.formula, rancs, x.factory) :: connect(xs, rem)

        case Nil => Nil
      }

      def find_matching(what:immutable.List[FormulaOccurrence], where : immutable.List[FormulaOccurrence])
            : immutable.List[FormulaOccurrence]= what match {
        case x::xs =>
          val (y, rest) = remove_first(x,where)
          y :: find_matching(xs, rest)
        case Nil => Nil
      }

      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>

          val (rparent, parentmap) = IvyToRobinson(parent, map)
          val contracted  = (clause.antecedent ++ clause.succedent) filter (_.ancestors.size >1)
          require(contracted.size == 1, "Error: only one aux formula may have been factored!")
          val ianc = contracted(0).ancestors
          val aux::deleted = find_matching(ianc.toList, (rparent.vertex.antecedent ++ rparent.vertex.succedent).toList)
          val rproof = RFactor(rparent, aux, deleted, Substitution[FOLExpression]())
          (rproof, parentmap + ((id, rproof)))
      }




    /*
        case IResolution(id, exp, lit1, lit2, clause, parent1, parent2) =>
          (parent1,parent2) match {
            case (IInstantiate(id1,exp1,sub1, clause1, parent1), IInstantiate(id2,exp2,sub2, clause2, parent2) ) =>
              val shared_vars : Set[Var] = sub1.map.keySet.intersect(sub2.map.keySet)

              val new_vars : Map[Var,FOLTerm]=
                Map[Var,FOLTerm]() ++ (shared_vars map ((x:Var) => (x,x.variant(generator).asInstanceOf[FOLTerm])))

              val sub2_ = for ((key,value) <-  sub2.map) yield {
                if (shared_vars contains key)
                  (new_vars(key), value)
                else
                  (key,value)
              }

              val variant_sub = Substitution[FOLTerm](new_vars.toList)

              apply(iproof)

          }

    */
  }

  def getIndex(fo : FormulaOccurrence, c : Clause, d : Clause) : (Boolean, Int, Int) = {
    val index = c.antecedent.indexOf(fo)
    if (index < 0) {
      val index_ = c.succedent.indexOf(fo)
      if (index_ <0) throw new Exception("Error finding index of occurrence "+fo+ " in clause "+c)
      val dindex = d.succedent.indexWhere( _.formula == fo.formula )
      if (dindex <0) throw new Exception("Error finding occurrence of formula "+fo.formula+ " in clause "+d)
      (true, index_, dindex )
    }
    else {
      val dindex = d.antecedent.indexWhere( _.formula == fo.formula )
      if (dindex <0) throw new Exception("Error finding occurrence of formula "+fo.formula+ " in clause "+d)
      (false, index, dindex )
    }
  }

}
