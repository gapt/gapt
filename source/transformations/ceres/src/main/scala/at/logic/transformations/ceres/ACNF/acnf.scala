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
    val i = applySchemaSubstitution.toIntegerTerm(n)
    val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
    val resDeduction = InstantiateResSchema(res_schema_name, n)._2
    println("resDeduction :")
    printSchemaProof(resDeduction)
    val p1 = SchemaProofDB.get(proof_name).rec
    val pterm = ProjectionTermCreators.extract(p1, Set.empty[FormulaOccurrence], getCutAncestors(p1))
    val new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(k, i.asInstanceOf[IntegerTerm] )
    var sub = new SchemaSubstitution3(new_map)
    val ground = GroundingProjectionTerm(pterm, sub)
    val ground_unfold = UnfoldProjectionTerm(ground)
    val rm_arrow_ground_unfold = RemoveArrowRules(ground_unfold)
    val projSet = ProjectionTermToSetOfProofs(rm_arrow_ground_unfold).toList.filter(p =>
      ! p.root.antecedent.exists(f1 =>
        p.root.succedent.exists(f2 =>
          f1.formula.syntaxEquals(f2.formula)
        )
      ))

    projSet.foreach(p => println(printSchemaProof.sequentToString(p.root)))
    println("\n\n")
    val new_z_subst = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema3.rs"))
    ParseResSchema(new_z_subst)
    val ground_proj_set = projSet.map(set => GroundingProjections(set, fo2SubstDB.map.toMap)).toSet
    ground_proj_set.foreach(p => println(printSchemaProof.sequentToString(p.root)))
    val ro = p1.root
    val new_map1 = scala.collection.immutable.Map.empty[Var, HOLExpression] + Pair(k, i.asInstanceOf[IntegerTerm] )
    var subst = new SchemaSubstitution1(new_map1)
    val end_seq = FSequent(ro.antecedent.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])), ro.succedent.toList.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])))
    apply(resDeduction, ground_proj_set, end_seq)
  }
}
