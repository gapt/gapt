package at.logic.transformations.ceres.ACNF

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.occurrences.{defaultFormulaOccurrenceFactory, FormulaOccurrence}
import at.logic.calculi.slk._
import at.logic.algorithms.shlk._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.schema._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.algorithms.lk.getCutAncestors
import at.logic.transformations.ceres.UnfoldProjectionTerm._
import at.logic.transformations.ceres._
import clauseSchema._
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol._
import at.logic.calculi.resolution.instance.Instance
import at.logic.language.hol.Atom
import at.logic.language.lambda.types.Ti
import at.logic.language.lambda.types.To
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.IntZero
import scala.collection.immutable
import at.logic.calculi.resolution.base.Clause
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.language.lambda.substitutions.Substitution


object ACNF {
    def plugProjections(resRefutation: LKProof, groun_proj_set: Set[LKProof], end_seq: FSequent): LKProof = {
      resRefutation match {
        case Axiom(Sequent(Nil,Nil)) =>
            groun_proj_set.find(p => p.root.toFSequent == end_seq).get
        case Axiom(Sequent(Nil,succedent)) =>
            val set = groun_proj_set.filter(p => {
              println("1) "+p.root.succedent.map(fo => fo.formula));
              println("2) "+succedent.map(fo => fo.formula));
              p.root.succedent.map(fo => fo.formula).intersect(succedent.map(fo => fo.formula)).nonEmpty
            })
            set.head
        case Axiom(Sequent(antecedent,Nil)) =>
              val set = groun_proj_set.filter(p => p.root.antecedent.map(fo =>
                fo.formula).intersect(antecedent.map(fo => fo.formula)).nonEmpty)
              set.head
        case Axiom(Sequent(antecedent,succedent)) =>
              val set = groun_proj_set.filter(p =>
                p.root.antecedent.map(fo => fo.formula).intersect(antecedent.map(fo => fo.formula)).nonEmpty &&
                p.root.succedent.map(fo => fo.formula).intersect(succedent.map(fo => fo.formula)).nonEmpty)
              set.head

        case EquationLeft1Rule(p1,p2, root, occ1, occ2, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationLeft1Rule(pr1, pr2, occ1.formula, occ2.formula, main.formula)

        case EquationLeft2Rule(p1,p2, root, occ1, occ2, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationLeft2Rule(pr1, pr2, occ1.formula, occ2.formula, main.formula)

        case EquationRight1Rule(p1,p2, root, occ1, occ2, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationRight1Rule(pr1, pr2, occ1.formula, occ2.formula, main.formula)

        case EquationRight2Rule(p1,p2, root, occ1, occ2, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationRight2Rule(pr1, pr2, occ1.formula, occ2.formula, main.formula)


        case CutRule(up1, up2, _, a1, a2) => {
          val pr1 = plugProjections(up1, groun_proj_set, end_seq)
          val pr2 = plugProjections(up2, groun_proj_set, end_seq)
//          println("\n\npr1:")
//          println(pr1.root)
//          printSchemaProof(pr1)
//          println("pr2:")
//          println(pr2.root)
//          printSchemaProof(pr2)
          CutRule(pr1, pr2, a1.formula)
        }
        case ContractionLeftRule(up1, _, a1, a2, p) => ContractionLeftRule(plugProjections(up1, groun_proj_set, end_seq), a1.formula)
        case ContractionRightRule(up1, _, a1, a2, p) => ContractionRightRule(plugProjections(up1, groun_proj_set, end_seq), a1.formula)
        case _ => throw new Exception("\nMissing case in acnf !\n")
      }
    }

  //for the usual CERES method
  //TODO: The way it constructs the ACNF should be slightly changed in a way that it should use mapping from a clause to a projection
  def apply(resRefutation: LKProof, ground_proj_set: Set[LKProof], end_seq: FSequent): LKProof = {
    val filtered_ground_proj_set = filterProjectionSet(ground_proj_set.toList, end_seq).toSet
//    val p = plugProjections(resRefutation, filtered_ground_proj_set, end_seq)
    val p = plugProjections(resRefutation, ground_proj_set, end_seq)
    contractionNormalForm(p)
  }

  //for the CERESs method
  def apply(proof_name: String, res_schema_name: String, n: Int): LKProof = {
    val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
    //the resolution proof
    val resDeduction = InstantiateResSchema(res_schema_name, n)._2
    //println("resDeduction :")
//    printSchemaProof(resDeduction)
    //computing the projections
    val p1base = SchemaProofDB.get(proof_name).base
    val p1rec = SchemaProofDB.get(proof_name).rec
    val ptermBase = ProjectionTermCreators.extract(p1base, Set.empty[FormulaOccurrence], getCutAncestors(p1base))
    val ptermRec = ProjectionTermCreators.extract(p1rec, Set.empty[FormulaOccurrence], getCutAncestors(p1rec))
    val ground = GroundingProjectionTerm((ptermBase, ptermRec), n)
    val ground_unfold = UnfoldProjectionTerm(ground)
    val rm_arrow_ground_unfold = RemoveArrowRules(ground_unfold)
    val projSet = ProjectionTermToSetOfProofs(rm_arrow_ground_unfold)
//      .toList.filter(p =>
//      ! p.root.antecedent.exists(f1 =>
//        p.root.succedent.exists(f2 =>
//          f1.formula.syntaxEquals(f2.formula)
//        )
//      ))

//    projSet.foreach(p => println(printSchemaProof.sequentToString(p.root)))
    //println("\n\n")
//    val new_z_subst = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "trs.sys"))
//    ParseResSchema(new_z_subst)
    //hard-coded the substitution for projections : {z -> \lambda k. a}
    fo2SubstDB.clear
    val z = fo2Var(new VariableStringSymbol("z"))
    val a = at.logic.language.schema.foConst("a")
    val h = HOLAbs(k.asInstanceOf[Var], a)
    fo2SubstDB.add(z.asInstanceOf[fo2Var], h)
    val ground_proj_set = projSet.map(set => GroundingProjections(set, fo2SubstDB.map.toMap)).toSet
//    ground_proj_set.foreach(p => println(printSchemaProof.sequentToString(p.root)))
    val end_seq = if (n == 0) {
      val ro = p1base.root
      val new_map1 = scala.collection.immutable.Map.empty[Var, HOLExpression] + Pair(k, IntZero() )
      var subst = new SchemaSubstitution1(new_map1)
      FSequent(ro.antecedent.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])), ro.succedent.toList.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])))
    } else {
      val ro = p1rec.root
      val new_map1 = scala.collection.immutable.Map.empty[Var, HOLExpression] + Pair(k, applySchemaSubstitution.toIntegerTerm(n-1) )
      var subst = new SchemaSubstitution1(new_map1)
      FSequent(ro.antecedent.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])), ro.succedent.toList.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])))
    }
    apply(resDeduction, ground_proj_set, end_seq)
  }

  /*
  //this only works for regular first order proofs
  def calculateGroundSubstitutions(proj : immutable.Set[LKProof], rp : RobinsonResolutionProof) : List[(HOLVar, HOLExpression)] = {
    //collect the initial axioms
    val raxioms : List[Clause] = rp.nodes.foldLeft(List[Clause]())( (list,el) =>
      el match {
      case InitialClause(clause) => clause::list ;
      case _ => list}
    )

    for (ax <- raxioms) yield {
      val axant = ax.toFSequent.antecedent
      val axsuc = ax.toFSequent.succedent

      def findmatchingprojection(p:LKProof) : Option[List[(HOLVar, HOLExpression)]] = {
        val root = p.root.toFSequent
        val pant = root.antecedent
        val psuc = root.succedent
        val pospairs  = getpairs(axsuc.toList, psuc.toList)
        val negpairs = getpairs(axant.toList, pant.toList)
        val pairs = for (pos <- pospairs; neg <- negpairs) yield { pos ++ neg }
        //FOLMatchingAlgorithm.matchSetOfTuples(Nil, )
        var result : Option[List[(HOLVar, HOLExpression)]] = None
        var candidates = pairs
        while (candidates.nonEmpty && result.isEmpty) {
          val candidate : List[(FOLFormula, FOLFormula)] = candidates.head.asInstanceOf[List[(FOLFormula, FOLFormula)]]
          candidates = candidates.tail
          val restrictedvars = candidate.flatMap(_._1.freeVariables)
          FOLMatchingAlgorithm.matchSetOfTuples(restrictedvars, candidate, Nil) match {
            case Some((Nil, r)) => result = Some(r.asInstanceOf[List[(HOLVar, HOLExpression)]])
            case _ => ;
          }
        }

        result
      }

      List[(HOLVar, HOLExpression)]()
    }
  } */

  def removeFirst[T](t:T, l:List[T]) : List[T] = l match {
    case x::xs => if (x==t) xs else x::removeFirst(t,xs)
    case Nil => Nil
  }

  def getpairs[T](l1 : List[T], l2 : List[T]) : List[List[(T,T)]]= (l1,l2) match {
    case (Nil, _) => Nil
    case (_, Nil) => throw new Exception("Second list in match search is not large enough!")
    case (x::xs, _) =>
      for (l <- l2) yield {
        ((x,l)::getpairs(xs, removeFirst(x,l2))).asInstanceOf[List[(T,T)]]
      }
  }

}

//apply contractions to the proof with formula repetitions
object contractionNormalForm {
  def apply(p: LKProof): LKProof = {
    val ant = p.root.antecedent.map(x => x.formula)
    val suc = p.root.succedent.map(x => x.formula)

    val ant1 = ant.map(f => ant.filter(f1 => f1 ==f)).filter(l => l.length > 1)
    val suc1 = suc.map(f => suc.filter(f1 => f1 ==f)).filter(l => l.length > 1)
    if(ant1.isEmpty && suc1.isEmpty)
      return p
    else
      if(ant1.isEmpty) {
        apply(ContractionRightRule(p, suc1.head.head))
      }
      else {
        apply(ContractionLeftRule(p, ant1.head.head))
      }
  }
}

/*This gives a ground substitution of the indexed variables.
  This substitution shold be applied to the projections in order
  to obtain a set of ground projections which should be plugged into the
  ground resolution proof (transformed to an LK proof, i.e. contains only cut inferences!)
  TODO: This should be done automatically! The transformation
  of the clause set to a TPTP problem renames the
  indexed variables z(i) to v_i. Then, the v_i is
  instantiated. This object maps manually z(i) to the corresponding ground term.
  This mapping should be done automatically somehow.
*/
object getInstantiationsOfTheIndexedFOVars {
  def apply1(rp: RobinsonResolutionProof): List[(HOLVar, HOLExpression)] = {
    rp match {
      case Instance(seq, parent1, sub) => sub.map.head.asInstanceOf[(HOLVar, HOLExpression)]::apply1(parent1)
      case InitialClause(clause) => List()
      case Variant(clause, parent1, sub) => sub.map.head.asInstanceOf[(HOLVar, HOLExpression)]::apply1(parent1)
      case Factor(clause, parent1, aux, sub) => apply1(parent1)
      case Resolution(clause, parent1, parent2, lit1, lit2, sub) => apply1(parent1):::apply1(parent2)
      case Paramodulation(clause, parent1, parent2, lit1, lit2, sub) => apply1(parent1):::apply1(parent2)
    }
  }
  def apply(rp: RobinsonResolutionProof): List[(HOLVar, HOLExpression)] = renameVVarToZVar(apply1(rp))
}


//TODO: This object should be removed.
//The map should be obtained from the transformation to TPTP format.
object renameVVarToZVar {
  def apply(l: List[(HOLVar, HOLExpression)]): List[(HOLVar, HOLExpression)] = {
    l.map(pair => {
      val new_var0 = indexedFOVar(new VariableStringSymbol("z"), IntZero())
      val new_var1 = indexedFOVar(new VariableStringSymbol("z"), Succ(IntZero()))

      //TODO: Conpute the index correctly
//      val new_name = pair._1.name.toString.tail
//      val new_var = FOLVar(new VariableStringSymbol("z"+new_name))
      (new_var0,pair._2)::(new_var1,pair._2)::Nil
    }).flatten
  }
}

// Transforms the clauses in the resolution LK proof to HOL
// in order the projections to be plugged easier in the
// resolution refutation skeleton.
object folToSHOL {
  def apply1(exp: FOLExpression): HOLExpression = {
    exp match {
      case FOLConst(name) => HOLConst(name, Ti())
      case at.logic.language.fol.Function(name, args) => {
        val func = HOLConst(new ConstantStringSymbol(name.toString()), Ti()->Ti())
        at.logic.language.hol.Function(func, args.map(f => apply1(f)))
      }
      case _ => throw new Exception("\nThere is a missing case in folToSHOL, but it should not be!\n")
    }
  }
  def apply(f: HOLFormula): HOLFormula = {
    f match {
      case Atom(name, args) => {
        val pred = HOLConst(new ConstantStringSymbol(name.toString()), Ti()->To())
        val new_args = args.map(f => apply1(f.asInstanceOf[FOLExpression]))
        at.logic.language.hol.Atom(pred, new_args)
      }
    }
  }
}


// Converts a first-order resolution LK proof (i.e. with cut-inferences only) to a HOL LK proof
object ConvertCutsToHOLFormulasInResProof {
  def apply(p: LKProof): LKProof = {
    p match {
      case Axiom(seq) => {
        val ant = seq.antecedent.map(fo => defaultFormulaOccurrenceFactory.createFormulaOccurrence(folToSHOL(fo.formula.asInstanceOf[FOLFormula]), Nil))
        val succ = seq.succedent.map(fo => defaultFormulaOccurrenceFactory.createFormulaOccurrence(folToSHOL(fo.formula.asInstanceOf[FOLFormula]), Nil))
        Axiom(Sequent(ant,succ))
      }
      case CutRule(up1, up2, _, a1, a2) => {
        val up11 = apply(up1)
        val up22 = apply(up2)
        CutRule(up11, up22, folToSHOL(a1.formula))
      }
      case _ => throw new Exception("\nERROR : Rule other then Axiom and CutRule !\n")
    }
  }
}

//does not work for schemata proofs
object SubstituteProof {
  def subapp(f: HOLFormula, sub:Substitution[HOLExpression]) = sub(f).asInstanceOf[HOLFormula]
  def subapp(f: FormulaOccurrence, sub:Substitution[HOLExpression]) = sub(f.formula).asInstanceOf[HOLFormula]
  def remove_from_sub(v:Var, sub:Substitution[HOLExpression]) = Substitution[HOLExpression](sub.map.filterNot( x => x._1 == v  ))

  def apply(proof: LKProof, sub:Substitution[HOLExpression]) : LKProof = proof match {
    case Axiom(s) =>
      val fs = s.toFSequent
      val ant : immutable.Seq[Formula] = fs.antecedent.map(sub(_).asInstanceOf[Formula])
      val suc : immutable.Seq[Formula] = fs.succedent.map(sub(_).asInstanceOf[Formula])
      val inf = Axiom(ant, suc )
      inf

    case WeakeningLeftRule(p, root, aux) =>
      val rp = apply(p, sub)
      WeakeningLeftRule(rp, subapp(aux,sub) )
    case WeakeningRightRule(p, root, aux) =>
      val rp = apply(p, sub)
      WeakeningRightRule(rp, subapp(aux, sub))
    case ContractionLeftRule(p,root,occ1,occ2,main) =>
      val rp = apply(p, sub)
      ContractionLeftRule(rp,subapp(occ1, sub))
    case ContractionRightRule(p,root,occ1,occ2,main) =>
      val rp = apply(p, sub)
      ContractionRightRule(rp,subapp(occ1, sub) )

    case AndLeft1Rule(p,root,aux1,aux2) =>
      val rp = apply(p, sub)
      AndLeft1Rule(rp, subapp(aux1,sub), subapp(aux2, sub))
    case AndLeft2Rule(p,root,aux1,aux2) =>
      val rp = apply(p, sub)
      AndLeft2Rule(rp, subapp(aux1,sub), subapp(aux2, sub))
    case AndRightRule(p1,p2,root,aux1, aux2,main) =>
      val rp1 = apply(p1, sub)
      val rp2 = apply(p2, sub)
      AndRightRule(rp1, rp2, subapp(aux1,sub), subapp(aux2, sub))
    case OrLeftRule(p1,p2,root,aux1, aux2,main) =>
      val rp1 = apply(p1, sub)
      val rp2 = apply(p2, sub)
      OrLeftRule(rp1, rp2, subapp(aux1,sub), subapp(aux2, sub))
    case OrRight1Rule(p,root,aux1,aux2) =>
      val rp = apply(p, sub)
      OrRight1Rule(rp, subapp(aux1,sub), subapp(aux2, sub))
    case OrRight2Rule(p,root,aux1,aux2) =>
      val rp = apply(p, sub)
      OrRight2Rule(rp, subapp(aux1,sub), subapp(aux2, sub))
    case ImpLeftRule(p1,p2,root,aux1, aux2,main) =>
      val rp1 = apply(p1, sub)
      val rp2 = apply(p2, sub)
      ImpLeftRule(rp1, rp2, subapp(aux1,sub), subapp(aux2, sub))
    case ImpRightRule(p,root,aux1,aux2,main) =>
      val rp = apply(p, sub)
      ImpRightRule(rp, subapp(aux1,sub), subapp(aux2, sub))

    case EquationLeft1Rule(p1,p2,root,aux1, aux2, main) =>
      val rp1 = apply(p1, sub)
      val rp2 = apply(p2, sub)
      EquationLeft1Rule(rp1, rp2, subapp(aux1,sub), subapp(aux2, sub), subapp(main,sub))
    case EquationLeft2Rule(p1,p2,root,aux1, aux2, main) =>
      val rp1 = apply(p1, sub)
      val rp2 = apply(p2, sub)
      EquationLeft2Rule(rp1, rp2, subapp(aux1,sub), subapp(aux2, sub), subapp(main,sub))
    case EquationRight1Rule(p1,p2,root,aux1, aux2, main) =>
      val rp1 = apply(p1, sub)
      val rp2 = apply(p2, sub)
      EquationRight1Rule(rp1, rp2, subapp(aux1,sub), subapp(aux2, sub), subapp(main,sub))
    case EquationRight2Rule(p1,p2,root,aux1, aux2, main) =>
      val rp1 = apply(p1, sub)
      val rp2 = apply(p2, sub)
      EquationRight2Rule(rp1, rp2, subapp(aux1,sub), subapp(aux2, sub), subapp(main,sub))

    case ForallLeftRule(p, root, aux, main, term) =>
      val rp = apply(p, sub)
      ForallLeftRule(rp, subapp(aux,sub), subapp(main,sub), sub(term))
    case ExistsRightRule(p, root, aux, main, term) =>
      val rp = apply(p, sub)
      ExistsRightRule(rp, subapp(aux,sub), subapp(main,sub), sub(term))

    case ForallRightRule(p, root, aux, main, eigenvar) =>
      val rsub = remove_from_sub(eigenvar, sub)
      val rp = apply(p, rsub)
      ForallLeftRule(rp, subapp(aux,rsub), subapp(main,rsub), eigenvar)
    case ExistsLeftRule(p, root, aux, main, eigenvar) =>
      val rsub = remove_from_sub(eigenvar, sub)
      val rp = apply(p, rsub)
      ExistsRightRule(rp, subapp(aux,rsub), subapp(main,rsub), eigenvar)


  }
}


// applies the ground substitution obtained from the resolution refutation
//TODO: this method does not care for bindings! Cvetan, please fix it!
object renameIndexedVarInProjection {
  def apply(p: LKProof, pair: Tuple2[Var, HOLExpression]): LKProof = {
//    println("p.rule = "+p.rule)
    p match {
      case Axiom(seq) => Axiom(Sequent(seq.antecedent.map(fo => fo.factory.createFormulaOccurrence(renameVar(fo.formula, pair), Nil)), seq.succedent.map(fo => fo.factory.createFormulaOccurrence(renameVar(fo.formula, pair), Nil) )))
      case WeakeningLeftRule(up, _, p1) => WeakeningLeftRule(apply(up,pair), renameVar(p1.formula,pair))
      case WeakeningRightRule(up, _, p1) => WeakeningRightRule(apply(up,pair), renameVar(p1.formula,pair))
      case ContractionLeftRule(up, _, a1, a2, _) => ContractionLeftRule(apply(up,pair), renameVar(a1.formula,pair))
      case ContractionRightRule(up, _, a1, a2, _) => ContractionRightRule(apply(up,pair), renameVar(a1.formula, pair))
      case AndLeft1Rule(up, _, a, p) => AndLeft1Rule(apply(up,pair), renameVar(a.formula, pair), renameVar(p.formula, pair))
      case AndLeft2Rule(up, _, a, p) => AndLeft2Rule(apply(up,pair), renameVar(a.formula, pair), renameVar(p.formula, pair))
      case AndRightRule(up1, up2, _, a1, a2, _) => AndRightRule(apply(up1,pair), apply(up2,pair), renameVar(a1.formula,pair), renameVar(a2.formula, pair))
      case OrLeftRule(up1, up2, _, a1, a2, _) => OrLeftRule(apply(up1,pair), apply(up2,pair), renameVar(a1.formula,pair), renameVar(a2.formula, pair))
      case OrRight1Rule(up, _, a, p) => OrRight1Rule(apply(up,pair), renameVar(a.formula,pair), renameVar(p.formula,pair))
      case OrRight2Rule(up, _, a, p) => OrRight2Rule(apply(up,pair), renameVar(a.formula,pair), renameVar(p.formula,pair))
      case ImpRightRule(up, _, a1, a2, _) => ImpRightRule(apply(up,pair), renameVar(a1.formula,pair), renameVar(a2.formula,pair))
      case ImpLeftRule(up1, up2, _, a1, a2, _) => ImpLeftRule(apply(up1,pair), apply(up2,pair), renameVar(a1.formula,pair), renameVar(a2.formula,pair))
      case NegLeftRule(up, _, a, p) => NegLeftRule(apply(up,pair), renameVar(a.formula,pair))
      case NegRightRule(up, _, a, p) => NegRightRule(apply(up,pair), renameVar(a.formula,pair))
      case ForallLeftRule(up, seq, a, p, t) => ForallLeftRule(apply(up,pair), renameVar(a.formula,pair), renameVar(p.formula,pair), renameVar.apply1(t,pair))
      case ExistsRightRule(up, _, a, p, t) => ExistsRightRule(apply(up,pair), renameVar(a.formula,pair), renameVar(p.formula,pair), renameVar.apply1(t,pair))
        //TODO: Implement ForallRight and ExistsLeft! Cvetan please fix it!
      case _ => throw new Exception("\nMissing case in GroundingProjections !\n"+p.rule)
    }
  }
}

//renames the indexed variable in atom
object renameVar {
  def apply1(exp: HOLExpression, pair: Tuple2[Var, HOLExpression]): HOLExpression = {
    println("renameVar, exp = "+exp)
    exp match {
      case v:indexedFOVar => {
//        println("   indexedFOVar = "+exp)
        if(v.asInstanceOf[Var] == pair._1)
          return pair._2
        else
          return v
      }
      case foc:foConst => {
//        println("   foConst = "+exp)
        HOLConst(new ConstantStringSymbol(foc.name.toString),Ti())
      }
//      case at.logic.language.fol.Function(name, args) => {
////        println("   fol.Function = "+exp)
//        //val func = HOLConst(new ConstantStringSymbol(name.toString()), Ti()->Ti())
////        println("   exp "+exp)
//        println("   new_args of "+args)
//        val new_args = args.map(f => apply1(f, pair).asInstanceOf[FOLTerm])
//        at.logic.language.fol.Function(name, new_args)
//      }
      case Succ(arg) => {
//        println("   Succ = "+exp)
        Succ(apply1(arg, pair))
      }
      case sTerm(f,i,args) => {
//        println("   sTerm = "+exp)
        sTerm(f,i,args.map(x => apply1(x,pair)))
      }
      case at.logic.language.hol.Function(name, args, typ) if args.size > 0=> {
//        println("   hol.Function = "+exp)
//        println("   typ = "+typ)
        val func = HOLConst(new ConstantStringSymbol(name.toString()), Ti()->Ti())
//        val func = HOLVar(new VariableStringSymbol(name.toString()), Ti()->Ti())
        at.logic.language.hol.Function(func, args.map(f => apply1(f, pair)))
      }
      case _ => {
//        println("   case _ => "+exp)
        exp
      }//throw new Exception("\nThere is a missing case in folToSHOL, but it should not be!\n")
    }
  }
  def apply(f: HOLFormula, pair: Tuple2[Var, HOLExpression]): HOLFormula = {
    f match {
      case Atom(name, args) => {
        val new_args = args.map(f => apply1(f, pair))
        at.logic.language.hol.Atom(new ConstantStringSymbol(name.toString()), new_args)
      }
      case at.logic.language.hol.Neg(form) => at.logic.language.hol.Neg(apply(form,pair))
      case at.logic.language.hol.Imp(form1,form2) => at.logic.language.hol.Imp(apply(form1,pair), apply(form2,pair))
      case at.logic.language.hol.And(form1,form2) => at.logic.language.hol.And(apply(form1,pair), apply(form2,pair))
      case at.logic.language.hol.Or(form1,form2) => at.logic.language.hol.Or(apply(form1,pair), apply(form2,pair))
      case _ => f//throw new Exception("\nThe formula should be atomic!\n")
    }
  }
}