package at.logic.transformations.ceres

import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import at.logic.algorithms.shlk._
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.slk._
import at.logic.language.fol.Utils
import at.logic.language.schema.{Substitution => SchemaSubstitution, SchemaVar, SchemaFormula, IndexedPredicate, IntVar, IntZero, IntegerTerm, Succ}
import at.logic.utils.ds.Multisets
import at.logic.utils.ds.Multisets.Multiset
import at.logic.utils.ds.trees.BinaryTree
import at.logic.utils.ds.trees.LeafTree
import at.logic.utils.ds.trees.Tree
import at.logic.utils.ds.trees.UnaryTree
import scala.collection.immutable.HashMap
import struct.StructCreators
import struct.TypeSynonyms
import struct.cutOccConfigToCutConfig

object RelevantCC {
  def apply(proof_name: String) = {
    val s = SchemaProofDB.toList.map(pair => genCC(pair._1)) //for console
    val spt = SchemaProofDB.toList.map(pair => genCCProofTool(pair._1))
    val sptb = SchemaProofDB.toList.map(pair => genCCProofToolBase(pair._1))

    val l_step = Utils.removeDoubles(List((proof_name, Set.empty[FormulaOccurrence]))::spt).filter(x => x.nonEmpty)
    val l_base = Utils.removeDoubles(List((proof_name, Set.empty[FormulaOccurrence]))::sptb).filter(x => x.nonEmpty)
    val pair = (l_step, l_base)
    pair
  }

  def genCC(proof_name: String): List[(String, Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten
    val l = Utils.removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)
    l.map(pair => (pair._1, (pair._2._1 ::: pair._2._1).toSet ))
  }



  def genCCProofTool(proof_name: String): List[(String, Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten
    val l = Utils.removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)
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
      val k = IntVar("k")
      val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), IntZero().asInstanceOf[IntegerTerm] )
      var sub = SchemaSubstitution(new_map)
      val groundccant = pair._2._1.map(fo => sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])))
      val groundccsucc = pair._2._2.map(fo => sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])))
      val s = (seq.antecedent.filter(fo => groundccant.contains(fo.formula)), seq.succedent.filter(fo => groundccsucc.contains(fo.formula)))

      (pair._1, s)
    })
    Utils.removeDoubles(cclistbase).filter(pair =>
      pair._2._1.nonEmpty || pair._2._2.nonEmpty).map(pair =>
      (pair._1, (pair._2._1.toSet ++ pair._2._2.toSet) ))
  }


  def getCC(p: LKProof, omega: List[FormulaOccurrence], p_old: LKProof): List[(String, (List[FormulaOccurrence], List[FormulaOccurrence]))] = p match {
    case SchemaProofLinkRule( seq, proof_name, index::_ ) => {
      val cut_omega_anc = getCutAncestors(p_old) ++ getAncestors(omega.toSet)
      val seq1 = SchemaProofDB.get(proof_name).rec.root
      val len = StepMinusOne.lengthVar(index.asInstanceOf[IntegerTerm])
      val foccsInSeqAnt = seq.antecedent.filter(fo => cut_omega_anc.contains(fo))
      val foccsInSeqSucc = seq.succedent.filter(fo => cut_omega_anc.contains(fo))
      var new_map = Map.empty[SchemaVar, IntegerTerm]
      var sub = SchemaSubstitution(new_map)
      if (len == 0)
        new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Succ(index.asInstanceOf[IntegerTerm]) )
      else
      if (len == 1)
        new_map = Map.empty[SchemaVar, IntegerTerm] 
      else {
        val k = IntVar("k")
        new_map  = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, StepMinusOne.intTermPlus(k, len-1 ))
        sub = SchemaSubstitution(new_map)
        val newccAnt = seq1.antecedent.toList.filter(fo => foccsInSeqAnt.map(foo => foo.formula).contains(sub(fo.formula.asInstanceOf[SchemaFormula])))
        val newccSucc = seq1.succedent.toList.filter(fo => foccsInSeqSucc.map(foo => foo.formula).contains(sub(fo.formula.asInstanceOf[SchemaFormula])))
        return (proof_name, (newccAnt, newccSucc))::Nil
      }
      sub = SchemaSubstitution(new_map)
      val fccAnt = foccsInSeqAnt.map(fo => sub(fo.formula.asInstanceOf[SchemaFormula]))
      val fccSucc = foccsInSeqSucc.map(fo => sub(fo.formula.asInstanceOf[SchemaFormula]))
      val fcc = fccAnt ++ fccSucc
      (proof_name, (seq1.antecedent.filter(fo => fcc.contains(fo.formula)).toList, seq1.succedent.filter(fo => fcc.contains(fo.formula)).toList))::Nil
    }
    case Axiom(so) => List.empty[(String, (List[FormulaOccurrence], List[FormulaOccurrence]))]
    case UnaryTree(_,up) => getCC(up.asInstanceOf[LKProof], omega, p_old)
    case BinaryTree(_, up1, up2) => getCC(up1.asInstanceOf[LKProof], omega, p_old) ++ getCC(up2.asInstanceOf[LKProof], omega, p_old)
  }
}
