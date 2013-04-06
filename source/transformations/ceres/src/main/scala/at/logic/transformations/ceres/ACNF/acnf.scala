package at.logic.transformations.ceres.ACNF

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.occurrences.{defaultFormulaOccurrenceFactory, FormulaOccurrence}
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.algorithms.shlk._
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.typedLambdaCalculus.{App, AppN, LambdaExpression, Var}
import at.logic.language.lambda.types.FunctionType._
import at.logic.language.lambda.types.To._
import at.logic.language.lambda.types._
import at.logic.language.hol.Atom._
import at.logic.language.schema.foTerm._
import at.logic.language.schema._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.algorithms.lk.getCutAncestors._
import at.logic.algorithms.lk.{getCutAncestors, addContractions, getAncestors}
import at.logic.transformations.ceres.GroundingProjectionTerm._
import at.logic.transformations.ceres.UnfoldProjectionTerm._
import at.logic.transformations.ceres.RemoveArrowRules._
import at.logic.transformations.ceres.ProjectionTermToSetOfProofs._
import at.logic.transformations.ceres._
import clauseSchema._
import java.io.{FileInputStream, InputStreamReader}
import java.io.File.separator
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol._
import at.logic.calculi.resolution.instance.Instance
import at.logic.calculi.proofs.NullaryProof
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.FunctionType.apply
import at.logic.transformations.ceres.UnfoldProjectionTerm.apply
import at.logic.algorithms.lk.getCutAncestors.apply
import at.logic.transformations.ceres.ProjectionTermToSetOfProofs.apply
import at.logic.transformations.ceres.RemoveArrowRules.apply
import at.logic.language.hol.Atom.apply
import at.logic.language.lambda.types.To.apply
import at.logic.transformations.ceres.GroundingProjectionTerm.apply
import at.logic.calculi.slk.AndEquivalenceRule1.apply
import at.logic.language.schema.foTerm.apply
import at.logic.language.schema.IntZero
import at.logic.language.lambda.types.Ti
import at.logic.language.lambda.types.FunctionType.apply
import at.logic.transformations.ceres.UnfoldProjectionTerm.apply
import at.logic.algorithms.lk.getCutAncestors.apply
import at.logic.transformations.ceres.ProjectionTermToSetOfProofs.apply
import at.logic.language.hol.Atom.apply
import at.logic.transformations.ceres.RemoveArrowRules.apply
import at.logic.language.lambda.types.To.apply
import at.logic.transformations.ceres.GroundingProjectionTerm.apply
import at.logic.calculi.slk.AndEquivalenceRule1.apply
import at.logic.language.schema.foTerm.apply
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.To
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.IntZero
import scala.Tuple2
import at.logic.language.hol.Atom
import at.logic.language.lambda.types.Ti
import at.logic.language.lambda.types.FunctionType.apply
import at.logic.transformations.ceres.UnfoldProjectionTerm.apply
import at.logic.algorithms.lk.getCutAncestors.apply
import at.logic.transformations.ceres.ProjectionTermToSetOfProofs.apply
import at.logic.language.hol.Atom.apply
import at.logic.transformations.ceres.RemoveArrowRules.apply
import at.logic.language.lambda.types.To.apply
import at.logic.transformations.ceres.GroundingProjectionTerm.apply
import at.logic.calculi.slk.AndEquivalenceRule1.apply
import at.logic.language.schema.foTerm.apply
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.To
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.IntZero
import scala.Tuple2


object ACNF {
    def plugProjections(resRefutation: LKProof, groun_proj_set: Set[LKProof], end_seq: FSequent): LKProof = {
      resRefutation match {
        case Axiom(seq) => {
          println("\nresRefutation.root = "+resRefutation.root)
          if(seq.antecedent.isEmpty && seq.succedent.isEmpty) {
            return groun_proj_set.find(p => p.root.toFSequent == end_seq).get
          }
          //println("seq = "+printSchemaProof.sequentToString(seq))
          if(seq.antecedent.isEmpty) {
            val set = groun_proj_set.filter(p => p.root.succedent.map(fo => fo.formula).intersect(seq.succedent.map(fo => fo.formula)).nonEmpty)
            println("\nant.Empty")
            println("projection.root : "+set.head.root)
            return set.head
          }
          else
            if(seq.succedent.isEmpty) {
              val set = groun_proj_set.filter(p => p.root.antecedent.map(fo => fo.formula).intersect(seq.antecedent.map(fo => fo.formula)).nonEmpty)
              println("\nsucc.Empty")
              println("projection.root : "+set.head.root)
              return set.head
            }
            else {
              val set = groun_proj_set.filter(p => p.root.antecedent.map(fo => fo.formula).intersect(seq.antecedent.map(fo => fo.formula)).nonEmpty && p.root.succedent.map(fo => fo.formula).intersect(seq.succedent.map(fo => fo.formula)).nonEmpty)
              println("\n(ant & succ)Empty")
              println("projection.root : "+set.head.root)
              return set.head
            }
        }
        case CutRule(up1, up2, _, a1, a2) => {
          val pr1 = plugProjections(up1, groun_proj_set, end_seq)
          val pr2 = plugProjections(up2, groun_proj_set, end_seq)
          println("\n\npr1:")
          println(pr1.root)
//          printSchemaProof(pr1)
          println("pr2:")
          println(pr2.root)
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
      val new_var = indexedFOVar(new VariableStringSymbol("z"), IntZero())
      //TODO: Conpute the index correctly
//      val new_name = pair._1.name.toString.tail
//      val new_var = FOLVar(new VariableStringSymbol("z"+new_name))
      (new_var,pair._2)
    })
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

// applies the ground substitution obtained from the resolution refutation
object renameIndexedVarInProjection {
  def apply(p: LKProof, pair: Tuple2[Var, HOLExpression]): LKProof = {
    //      println("p.rule = "+p.rule)
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
      case _ => throw new Exception("\nMissing case in GroundingProjections !\n"+p.rule)
    }
  }
}

//renames the indexed variable in atom
object renameVar {
  def apply1(exp: HOLExpression, pair: Tuple2[Var, HOLExpression]): HOLExpression = {
    exp match {
      case v:indexedFOVar => {
        if(v.asInstanceOf[Var] == pair._1)
          return pair._2
        else
          return v
      }
      case foc:foConst => HOLConst(new ConstantStringSymbol(foc.name.toString),Ti())
      case at.logic.language.fol.Function(name, args) => {
        val func = HOLConst(new ConstantStringSymbol(name.toString()), Ti()->Ti())
        at.logic.language.hol.Function(func, args.map(f => apply1(f, pair)))
      }
      case at.logic.language.hol.Function(name, args, _) => {
        val func = HOLConst(new ConstantStringSymbol(name.toString()), Ti()->Ti())
        at.logic.language.hol.Function(func, args.map(f => apply1(f, pair)))
      }
      case _ => exp//throw new Exception("\nThere is a missing case in folToSHOL, but it should not be!\n")
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