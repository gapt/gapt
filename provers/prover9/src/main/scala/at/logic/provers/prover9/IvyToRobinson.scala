package at.logic.provers.prover9.ivy.conversion
import at.logic.provers.prover9.ivy.{InitialClause => IInitialClause, Instantiate => IInstantiate, Resolution => IResolution, Paramodulation => IParamodulation, IvyResolutionProof, Flip}

import at.logic.calculi.resolution.robinson.{InitialClause => RInitialClause, Resolution => RResolution, Factor => RFactor, Variant => RVariant, Paramodulation => RParamodulation, RobinsonResolutionProof}
import at.logic.language.fol.{FOLExpression, FOLTerm, FOLFormula}
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, VariantGenerator, Var}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.resolution.instance.{Instance => RInstantiate}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.base.Clause

/**
 * Converts Ivy Proofs into Robinson Resolution Proofs
 */
object IvyToRobinson {
  val generator : VariantGenerator = new VariantGenerator( new {var c = 10000; def nextId = {c = c+1; c}} , "iv" )

  def apply(iproof : IvyResolutionProof) : RobinsonResolutionProof = iproof match {
    case IInitialClause(id, exp, clause) =>
      RInitialClause(clause.negative map (_.formula.asInstanceOf[FOLFormula]), clause.positive map (_.formula.asInstanceOf[FOLFormula]))
    case IInstantiate(id, exp, sub, clause, parent) =>
      RInstantiate(IvyToRobinson(parent), sub.asInstanceOf[Substitution[FOLExpression]])
    case IResolution(id, exp, lit1, lit2, clause, parent1, parent2) =>
      val rparent1 = IvyToRobinson(parent1)
      val rparent2 = IvyToRobinson(parent2)
      val (polarity1, _, index1) = getIndex(lit1, parent1.vertex, rparent1.vertex)
      val (polarity2, _, index2) = getIndex(lit2, parent2.vertex, rparent2.vertex)

      //println("Resolved clauses left:  "+parent1.vertex + " - "+rparent1.vertex)
      //println("Resolved clauses right: "+parent2.vertex + " - "+rparent2.vertex)
      //println("Resolution literals:"+lit1 +" "+lit2)
      //println("Resolution indices: "+ ((polarity1, index1)) + ((polarity2, index2)))

      (polarity1, polarity2) match {
        case (true,false) =>
          require(rparent1.vertex.succedent(index1).formula == lit1.formula, "Left parent literal must be correctly found!")
          require(rparent2.vertex.antecedent(index2).formula == lit2.formula,
            "Right parent literal "+lit2+" at pos "+ index2 +" must be correctly found!" + rparent2.vertex)

          RResolution(rparent1, rparent2, rparent1.vertex.succedent(index1), rparent2.vertex.antecedent(index2), Substitution[FOLExpression]())
        case (false,true) =>
          require(rparent1.vertex.antecedent(index1).formula == lit1.formula, "Left parent literal must be correctly found!")
          require(rparent2.vertex.succedent(index2).formula == lit2.formula,
            "Right parent literal "+lit2+" at pos "+ index2 +" must be correctly found!" + rparent2.vertex)

          RResolution(rparent2, rparent1, rparent2.vertex.succedent(index2), rparent1.vertex.antecedent(index1), Substitution[FOLExpression]())
        case _ => throw new Exception("Error in processing ivy proof: resolved literals "+lit1+" and "+lit2+
                                      " do not have different polarity!")
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
