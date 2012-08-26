package at.logic.transformations.ceres

import at.logic.algorithms.lk.getAncestors
import at.logic.algorithms.lk.getCutAncestors
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.fol.Utils
import at.logic.language.hol.HOLConst
import at.logic.language.hol.HOLExpression
import at.logic.language.hol.HOLFormula
import at.logic.language.hol.logicSymbols.ConstantSymbolA
import at.logic.language.hol.logicSymbols.LogicalSymbolsA
import at.logic.language.lambda.symbols.SymbolA
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.lambda.types.ImplicitConverters.fromString
import at.logic.language.schema.IndexedPredicate
import at.logic.language.schema.IntVar
import at.logic.language.schema.IntZero
import at.logic.language.schema.IntegerTerm
import at.logic.calculi.slk._
import at.logic.calculi.lk.quantificationRules.{ExistsRightRule, ExistsLeftRule, ForallRightRule, ForallLeftRule}
import at.logic.calculi.lk.propositionalRules._

//import at.logic.language.schema.SchemaFormula
import at.logic.language.schema.Succ
import at.logic.algorithms.shlk._
import at.logic.utils.ds.Multisets
import at.logic.utils.ds.Multisets.Multiset
import at.logic.utils.ds.trees.BinaryTree
import at.logic.utils.ds.trees.LeafTree
import at.logic.utils.ds.trees.Tree
import at.logic.utils.ds.trees.UnaryTree
import at.logic.algorithms.shlk._
import scala.collection.immutable.HashMap
import struct.StructCreators
import struct.TypeSynonyms
import struct.cutOccConfigToCutConfig

object RelevantCC {
  def apply(proof_name: String): List[List[(String, Set[FormulaOccurrence])]] = {
    val s = SchemaProofDB.toList.map(pair => genCC(pair._1)) //for console
    val spt = SchemaProofDB.toList.map(pair => genCCProofTool(pair._1))
    val sptb = SchemaProofDB.toList.map(pair => genCCProofToolBase(pair._1))

    val l = Utils.removeDoubles(List((proof_name, Set.empty[FormulaOccurrence]))::spt).filter(x => x.nonEmpty)
    println("\n\nl = " + l)
    l
  }

  def genCC(proof_name: String): List[(String, Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten
    val l = Utils.removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)
    //    l.foreach(pair => {
    //      println("\n\n\n"+pair._1 +" : ")
    //      pair._2._1.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    //      pair._2._2.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    //    })
    l.map(pair => (pair._1, (pair._2._1 ::: pair._2._1).toSet ))
  }



  def genCCProofTool(proof_name: String): List[(String, Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten
    val l = Utils.removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)
    // l.foreach(tri => {
    //  println("\n"+tri._1)
    //  tri._2._1.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    //  tri._2._2.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    // })
    l.map(pair => (pair._1, (pair._2._1 ::: pair._2._2).toSet ))
  }

  def genCCProofToolBase(proof_name: String): List[(String, Set[FormulaOccurrence])] = {
    val p_base = SchemaProofDB.get(proof_name).base
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(p_rec, pair._2._1 ::: pair._2._2, p_rec)).flatten

    val cclistbase = Utils.removeDoubles(cclist1 ::: cclist).map(pair =>{
      val seq = SchemaProofDB.get(pair._1).base.root
      val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
      val new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], IntZero().asInstanceOf[IntegerTerm] )
      var sub = new SchemaSubstitution1[HOLExpression](new_map)
      val groundccant = pair._2._1.map(fo => sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])))
      val groundccsucc = pair._2._2.map(fo => sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])))
      val s = (seq.antecedent.filter(fo => groundccant.contains(fo.formula)), seq.succedent.filter(fo => groundccsucc.contains(fo.formula)))

      (pair._1, s)
    })
    // cclistbase.foreach(pair => {
    //  println("\n\ncclistbase : "+pair._1)
    //  pair._2._1.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    //  pair._2._2.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    // })
    Utils.removeDoubles(cclistbase).filter(pair =>
      pair._2._1.nonEmpty || pair._2._2.nonEmpty).map(pair =>
      (pair._1, (pair._2._1.toSet ++ pair._2._2.toSet) ))
  }


  def getCC(p: LKProof, omega: List[FormulaOccurrence], p_old: LKProof): List[(String, (List[FormulaOccurrence], List[FormulaOccurrence]))] = p match {
    case SchemaProofLinkRule( seq, proof_name, index::_ ) => {
      val cut_omega_anc = getCutAncestors(p_old) ++ getAncestors(omega.toSet)
      val seq1 = SchemaProofDB.get(proof_name).rec.root
      val len = StepMinusOne.lengthVar(index)
      val foccsInSeqAnt = seq.antecedent.filter(fo => cut_omega_anc.contains(fo))
      val foccsInSeqSucc = seq.succedent.filter(fo => cut_omega_anc.contains(fo))
      var new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm]
      var sub = new SchemaSubstitution1[HOLExpression](new_map)
      if (len == 0)
        new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], Succ(index) )
      else
      if (len == 1)
        new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] //+ Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], index )
      else {
        val k = IntVar(new VariableStringSymbol("k"))
        new_map  = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(k.asInstanceOf[Var], StepMinusOne.intTermPlus(k, len-1 ))
        sub = new SchemaSubstitution1[HOLExpression](new_map)
        val newccAnt = seq1.antecedent.toList.filter(fo => foccsInSeqAnt.map(foo => foo.formula).contains(sub(fo.formula)))
        val newccSucc = seq1.succedent.toList.filter(fo => foccsInSeqSucc.map(foo => foo.formula).contains(sub(fo.formula)))
        return (proof_name, (newccAnt, newccSucc))::Nil
      }
      sub = new SchemaSubstitution1[HOLExpression](new_map)
      val fccAnt = foccsInSeqAnt.map(fo => sub(fo.formula))
      val fccSucc = foccsInSeqSucc.map(fo => sub(fo.formula))
      val fcc = fccAnt ++ fccSucc
      (proof_name, (seq1.antecedent.filter(fo => fcc.contains(fo.formula)).toList, seq1.succedent.filter(fo => fcc.contains(fo.formula)).toList))::Nil
    }
    case Axiom(so) => List.empty[(String, (List[FormulaOccurrence], List[FormulaOccurrence]))]
    case UnaryTree(_,up) => getCC(up.asInstanceOf[LKProof], omega, p_old)
    case BinaryTree(_, up1, up2) => getCC(up1.asInstanceOf[LKProof], omega, p_old) ++ getCC(up2.asInstanceOf[LKProof], omega, p_old)
  }



}