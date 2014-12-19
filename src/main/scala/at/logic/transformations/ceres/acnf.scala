
package at.logic.transformations.ceres.ACNF

import at.logic.algorithms.lk.getCutAncestors
import at.logic.algorithms.matching.FOLMatchingAlgorithm
import at.logic.algorithms.shlk._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.Clause
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.slk._
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.schema.{Substitution => SchemaSubstitution, SchemaExpression, IntVar, fo2Var, foConst, SchemaAbs, SchemaVar, unfoldSFormula, indexedFOVar, Succ, sTerm, IntZero, SchemaFormula, toIntegerTerm}
import at.logic.transformations.ceres.UnfoldProjectionTerm._
import at.logic.transformations.ceres._
import clauseSchema._

object ACNF {
    def plugProjections(resRefutation: LKProof, groun_proj_set: Set[LKProof], end_seq: FSequent): LKProof = {
      resRefutation match {
        case Axiom(Sequent(Nil,Nil)) =>
          groun_proj_set.find(p => p.root.toFSequent == end_seq).get
        case Axiom(Sequent(Nil,succedent)) =>
          val set = groun_proj_set.filter(p => {
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

        case EquationLeft1Rule(p1,p2, root, occ1, occ2,_, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationLeftRule(pr1, pr2, occ1.formula, occ2.formula, main.formula)

        case EquationLeft2Rule(p1,p2, root, occ1, occ2,_, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationLeftRule(pr1, pr2, occ1.formula, occ2.formula, main.formula)

        case EquationRight1Rule(p1,p2, root, occ1, occ2,_, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationRightRule(pr1, pr2, occ1.formula, occ2.formula, main.formula)

        case EquationRight2Rule(p1,p2, root, occ1, occ2,_, main) =>
          val pr1 = plugProjections(p1, groun_proj_set, end_seq)
          val pr2 = plugProjections(p2, groun_proj_set, end_seq)
          EquationRightRule(pr1, pr2, occ1.formula, occ2.formula, main.formula)


        case CutRule(up1, up2, _, a1, a2) => {
          val pr1 = plugProjections(up1, groun_proj_set, end_seq)
          val pr2 = plugProjections(up2, groun_proj_set, end_seq)
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
    val k = IntVar("k")
    //the resolution proof
    val resDeduction = InstantiateResSchema(res_schema_name, n)._2
    //computing the projections
    val p1base = SchemaProofDB.get(proof_name).base
    val p1rec = SchemaProofDB.get(proof_name).rec
    val ptermBase = ProjectionTermCreators.extract(p1base, Set.empty[FormulaOccurrence], getCutAncestors(p1base))
    val ptermRec = ProjectionTermCreators.extract(p1rec, Set.empty[FormulaOccurrence], getCutAncestors(p1rec))
    val ground = GroundingProjectionTerm((ptermBase, ptermRec), n)
    val ground_unfold = UnfoldProjectionTerm(ground)
    val rm_arrow_ground_unfold = RemoveArrowRules(ground_unfold)
    val projSet = ProjectionTermToSetOfProofs(rm_arrow_ground_unfold)

    //hard-coded the substitution for projections : {z -> \lambda k. a}
    fo2SubstDB.clear
    val z = fo2Var("z")
    val a = foConst("a")
    // a is const... wtf?????
    val h = SchemaAbs(k, a)
    fo2SubstDB.add(z, h)
    val ground_proj_set = projSet.map(set => GroundingProjections(set, fo2SubstDB.map.toMap)).toSet
    val end_seq = if (n == 0) {
      val ro = p1base.root
      val new_map1 = Map.empty[SchemaVar, SchemaExpression] + Tuple2(k, IntZero() )
      var subst = SchemaSubstitution(new_map1)
      FSequent(ro.antecedent.map(fo => unfoldSFormula(subst(fo.formula.asInstanceOf[SchemaFormula]))), ro.succedent.toList.map(fo => unfoldSFormula(subst(fo.formula.asInstanceOf[SchemaFormula]))))
    } else {
      val ro = p1rec.root
      val new_map1 = Map.empty[SchemaVar, SchemaExpression] + Tuple2(k, toIntegerTerm(n-1) )
      var subst = SchemaSubstitution(new_map1)
      FSequent(ro.antecedent.map(fo => unfoldSFormula(subst(fo.formula.asInstanceOf[SchemaFormula]))), ro.succedent.toList.map(fo => unfoldSFormula(subst(fo.formula.asInstanceOf[SchemaFormula]))))
    }
    apply(resDeduction, ground_proj_set, end_seq)
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

// applies the ground substitution obtained from the resolution refutation
//TODO: this method does not care for bindings! Cvetan, please fix it!
// Cvetan is no longer here, now what??
object renameIndexedVarInProjection {
  def apply(p: LKProof, pair: Tuple2[HOLVar, HOLExpression]): LKProof = {
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
      case ForallLeftRule(up, seq, a, p, t) => ForallLeftRule(apply(up,pair), renameVar(a.formula,pair), renameVar(p.formula,pair), renameVar(t,pair))
      case ExistsRightRule(up, _, a, p, t) => ExistsRightRule(apply(up,pair), renameVar(a.formula,pair), renameVar(p.formula,pair), renameVar(t,pair))
        //TODO: Implement ForallRight and ExistsLeft! Cvetan please fix it!
      case _ => throw new Exception("\nMissing case in GroundingProjections !\n"+p.rule)
    }
  }
}

//renames the indexed variable in atom
object renameVar {
  def apply(exp: HOLExpression, pair: Tuple2[HOLVar, HOLExpression]): HOLExpression = {
    exp match {
      case v:indexedFOVar => {
        if(v == pair._1)
          return pair._2
        else
          return v
      }
      case foc:foConst => {
        HOLConst(foc.name.toString,Ti)
      }
      case Succ(arg) => {
        Succ(apply(arg, pair).asInstanceOf[SchemaExpression])
      }
      case sTerm(f,i,args) => {
        sTerm(f,i,args.map(x => apply(x,pair).asInstanceOf[SchemaExpression]))
      }
      case Function(name, args, typ) if args.size > 0=> {
        val func = HOLConst(name.toString(), Ti->Ti)
        Function(func, args.map(f => apply(f, pair)))
      }
      case _ => exp
    }
  }
  def apply(f: HOLFormula, pair: Tuple2[HOLVar, HOLExpression]): HOLFormula = {
    f match {
      case Atom(name, args) => {
        val new_args = args.map(f => apply(f, pair))
        Atom(HOLConst(name.toString(), FunctionType(To, new_args.map(_.exptype))), new_args)
      }
      case Neg(form) => Neg(apply(form,pair))
      case Imp(form1,form2) => Imp(apply(form1,pair), apply(form2,pair))
      case And(form1,form2) => And(apply(form1,pair), apply(form2,pair))
      case Or(form1,form2) => Or(apply(form1,pair), apply(form2,pair))
      case _ => f
    }
  }
}

/*
object SubstituteProof {
  def subapp(f: HOLFormula, sub:Substitution) = sub(f)
  def subapp(f: FormulaOccurrence, sub:Substitution) = sub(f.formula)
  def remove_from_sub(v:HOLVar, sub:Substitution) = Substitution(sub.holmap.filterNot( x => x._1 == v  ))

  def apply(proof: LKProof, sub:Substitution) : LKProof =
    proof match {
      case Axiom(s) =>
        val fs = s.toFSequent
        val ant = fs.antecedent.map(sub(_))
        val suc = fs.succedent.map(sub(_))
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

      case CutRule(p1,p2, root, aux1, aux2) =>
        val rp1 = apply(p1, sub)
        val rp2 = apply(p2, sub)
        CutRule(rp1, rp2, subapp(aux1,sub))

      case NegLeftRule(p,root,aux1,primary) =>
        val rp = apply(p, sub)
        NegLeftRule(rp, subapp(aux1,sub))
      case NegRightRule(p,root,aux1,primary) =>
        val rp = apply(p, sub)
        NegRightRule(rp, subapp(aux1,sub))

      case AndLeft1Rule(p,root,aux1,main) =>
        val aux2 = main.formula match { case And(_,f) => f }
        val rp = apply(p, sub)
        AndLeft1Rule(rp, subapp(aux1,sub), subapp(aux2, sub))
      case AndLeft2Rule(p,root,aux2,main) =>
        val aux1 = main.formula match { case And(f,_) => f }
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
      case OrRight1Rule(p,root,aux1,main) =>
        val aux2 = main.formula match { case Or(_,f) => f }
        val rp = apply(p, sub)
        OrRight1Rule(rp, subapp(aux1,sub), subapp(aux2, sub))
      case OrRight2Rule(p,root,aux2,main) =>
        val aux1 = main.formula match { case Or(f,_) => f }
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
        ForallRightRule(rp, subapp(aux,rsub), subapp(main,rsub), eigenvar)
      case ExistsLeftRule(p, root, aux, main, eigenvar) =>
        val rsub = remove_from_sub(eigenvar, sub)
        val rp = apply(p, rsub)
        ExistsLeftRule(rp, subapp(aux,rsub), subapp(main,rsub), eigenvar)

      case DefinitionLeftRule(p, root, aux, main) =>
        val rp = apply(p, sub)
        DefinitionLeftRule(rp, subapp(aux,sub), subapp(main,sub))
      case DefinitionRightRule(p, root, aux, main) =>
        val rp = apply(p, sub)
        DefinitionRightRule(rp, subapp(aux,sub), subapp(main,sub))
    }
}
*/