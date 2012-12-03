package at.logic.transformations.ceres.ACNF

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.algorithms.shlk._
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.typedLambdaCalculus.{AppN, LambdaExpression, Var}
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


object ACNF {
    def plugProjections(resRefutation: LKProof, groun_proj_set: Set[LKProof]): LKProof = {
      resRefutation match {
        case Axiom(seq) => {
          println("seq = "+printSchemaProof.sequentToString(seq))
          if(seq.antecedent.isEmpty) {
            val set = groun_proj_set.filter(p => p.root.succedent.map(fo => fo.formula).intersect(seq.succedent.map(fo => fo.formula)).nonEmpty)
            set.head
          }
          else
            if(seq.succedent.isEmpty) {
              groun_proj_set.filter(p => p.root.antecedent.map(fo => fo.formula).intersect(seq.antecedent.map(fo => fo.formula)).nonEmpty).head
            }
            else {
              val set = groun_proj_set.filter(p => p.root.antecedent.map(fo => fo.formula).intersect(seq.antecedent.map(fo => fo.formula)).nonEmpty && p.root.succedent.map(fo => fo.formula).intersect(seq.succedent.map(fo => fo.formula)).nonEmpty).head
              println("set.size = "+set.size)
              set
            }
        }
        case CutRule(up1, up2, _, a1, a2) => CutRule(plugProjections(up1, groun_proj_set), plugProjections(up2, groun_proj_set), a1.formula)
        case ContractionLeftRule(up1, _, a1, a2, p) => ContractionLeftRule(plugProjections(up1, groun_proj_set), a1.formula)
        case ContractionRightRule(up1, _, a1, a2, p) => ContractionRightRule(plugProjections(up1, groun_proj_set), a1.formula)
        case _ => throw new Exception("\nMissing case in acnf !\n")
      }
    }

  //for the usual CERES method
  def apply(resRefutation: LKProof, groun_proj_set: Set[LKProof], end_seq: FSequent): LKProof = {
    val p = plugProjections(resRefutation, groun_proj_set)
    addContractions(p, end_seq)
  }

  //for the CERESs method
  def apply(proof_name: String, res_schema_name: String, n: Int): LKProof = {
    val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
    //the resolution proof
    val resDeduction = InstantiateResSchema(res_schema_name, n)._2
    println("resDeduction :")
    printSchemaProof(resDeduction)
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

    projSet.foreach(p => println(printSchemaProof.sequentToString(p.root)))
    println("\n\n")
//    val new_z_subst = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "trs.sys"))
//    ParseResSchema(new_z_subst)
    //hard-coded the substitution for projections : {z -> \lambda k. a}
    fo2SubstDB.clear
    val z = fo2Var(new VariableStringSymbol("z"))
    val a = foVar("a")
    val h = HOLAbs(k.asInstanceOf[Var], a)
    fo2SubstDB.add(z.asInstanceOf[fo2Var], h)
    val ground_proj_set = projSet.map(set => GroundingProjections(set, fo2SubstDB.map.toMap)).toSet
    ground_proj_set.foreach(p => println(printSchemaProof.sequentToString(p.root)))
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
