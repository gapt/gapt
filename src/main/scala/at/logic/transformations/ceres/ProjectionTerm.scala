
package at.logic.transformations.ceres

import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import at.logic.algorithms.shlk._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base.{FSequent, LKProof, Sequent}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.slk._
import at.logic.language.fol.Utils.{removeDoubles, removeDoubles3}
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols.LogicalSymbolA
import at.logic.language.lambda.symbols.SymbolA
import at.logic.language.lambda.types._
import at.logic.language.schema.{Substitution => SchemaSubstitution, SchemaFormula, IntegerTerm, SchemaVar, IntVar, IndexedPredicate, IntZero, unfoldSFormula, Succ, Pred, sIndTerm, unfoldSINDTerm, sTerm, unfoldSTerm, toIntegerTerm}
import at.logic.utils.ds.Multisets
import at.logic.utils.ds.Multisets.Multiset
import at.logic.utils.ds.trees.BinaryTree
import at.logic.utils.ds.trees.LeafTree
import at.logic.utils.ds.trees.Tree
import at.logic.utils.ds.trees.UnaryTree
import struct.StructCreators
import struct.TypeSynonyms
import struct.cutOccConfigToCutConfig
import struct.cutConfToString
import scala.collection.immutable.HashMap


trait ProjectionTerm

class pTimes(val rho: String, val left: ProjectionTerm, val right: ProjectionTerm,  val aux1: HOLFormula, val aux2: HOLFormula) extends ProjectionTerm
object pTimes {
  def apply(rho: String, left: ProjectionTerm, right: ProjectionTerm,  aux1: HOLFormula,  aux2: HOLFormula) : pTimes = {
    new pTimes(rho, left, right, aux1, aux2)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t : pTimes => Some((t.rho, t.left, t.right, t.aux1, t.aux2))
    case _ => None
  }
}

class pPlus(val seq1: Sequent, val seq2: Sequent, val left: ProjectionTerm, val right: ProjectionTerm, val w1: Sequent, val w2: Sequent) extends ProjectionTerm
object pPlus {
  def apply(seq1: Sequent, seq2: Sequent, left: ProjectionTerm, right: ProjectionTerm, w1: Sequent, w2: Sequent): pPlus = {
    new pPlus(seq1, seq2, left, right, w1, w2)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t : pPlus => Some((t.seq1, t.seq2, t.left, t.right, t.w1, t.w2))
    case _ => None
  }
}

class pUnary(val rho: String, val upper: ProjectionTerm, val auxl: List[HOLExpression]) extends ProjectionTerm
object pUnary {
  def apply(rho: String, upper: ProjectionTerm, auxl: List[HOLExpression]) = {
    new pUnary(rho, upper, auxl)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t : pUnary => Some((t.rho, t.upper, t.auxl))
    case _ => None
  }
}

class pProofLinkTerm(val seq: Sequent, val omega: Set[FormulaOccurrence], val proof_name: String, val index: IntegerTerm, val ccanc: Set[FormulaOccurrence]) extends ProjectionTerm
object pProofLinkTerm {
  def apply(seq: Sequent, omega: Set[FormulaOccurrence], proof_name: String, index: IntegerTerm, ccanc: Set[FormulaOccurrence]) = {
    new pProofLinkTerm(seq, omega, proof_name, index, ccanc)

  }
  def unapply(term : ProjectionTerm) = term match {
    case t: pProofLinkTerm => Some((t.seq, t.omega, t.proof_name, t.index, t.ccanc))
    case _ => None
  }
}

class pAxiomTerm(val seq: Sequent) extends ProjectionTerm
object pAxiomTerm {
  def apply(seq: Sequent) = {
    new pAxiomTerm(seq)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t : pAxiomTerm => Some(t.seq)
    case _ => None
  }
}

object ProjectionTermCreators {
   
  def relevantProj(main_proof: String) : List[(String, Tree[AnyRef])] = {
    val s = SchemaProofDB.toList.map(pair => genCC(pair._1)) //for console
    val spt = removeDoubles3(SchemaProofDB.toList.map(pair => genCCProofTool(pair._1)).flatten)
    val sptb = removeDoubles3(SchemaProofDB.toList.map(pair => genCCProofToolBase(pair._1)).flatten)
    val slpt  = (main_proof, extract(SchemaProofDB.get(main_proof).rec,  Set.empty[FormulaOccurrence], getCutAncestors(SchemaProofDB.get(main_proof).rec)) , Set.empty[FormulaOccurrence]) :: spt
    val slptb = (main_proof, extract(SchemaProofDB.get(main_proof).base, Set.empty[FormulaOccurrence], getCutAncestors(SchemaProofDB.get(main_proof).base)), (Set.empty[FormulaOccurrence], Set.empty[FormulaOccurrence])) :: sptb

    val l  = slpt.map(tri => {
      val k = IntVar("k")
      val trans_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, IntVar("n") )
      val trans_sub = SchemaSubstitution(trans_map)
      val seq = SchemaProofDB.get(tri._1).rec.root
      val ms = new Multisets.HashMultiset[HOLFormula](HashMap.empty[HOLFormula, Int])
      val ms11 = tri._3.filter(fo => seq.antecedent.contains(fo)).map(fo => trans_sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar]))).foldLeft(ms)((res,f) => res + f.asInstanceOf[HOLFormula])
      val ms22 = tri._3.filter(fo => seq.succedent.contains(fo)).map(fo => trans_sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar]))).foldLeft(ms)((res,f) => res + f.asInstanceOf[HOLFormula])
      val name = "\u039e("+ tri._1 +"_step, ("+cutConfToString( (ms11,ms22) ) + "))"
      ProjectionTermDB.put(name, tri._2)
      (name, PStructToExpressionTree(tri._2))
    }) ::: slptb.map(tri => {
      val k = IntVar("k")
      val trans1_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, IntVar("n") )
      val trans1_sub = SchemaSubstitution(trans1_map)
      val trans_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, IntZero() )
      val trans_sub = SchemaSubstitution(trans_map)
      val seq = SchemaProofDB.get(tri._1).rec.root
      val ms = new Multisets.HashMultiset[HOLFormula](HashMap.empty[HOLFormula, Int])
      val ms11 = seq.antecedent.filter(fo => tri._3._1.map(x => x.formula).contains(trans_sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])).asInstanceOf[HOLFormula])).foldLeft(ms)((res,fo) => res + trans1_sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])).asInstanceOf[HOLFormula])
      val ms22 =  seq.succedent.filter(fo => tri._3._2.map(x => x.formula).contains(trans_sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])).asInstanceOf[HOLFormula])).foldLeft(ms)((res,fo) => res + trans1_sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])).asInstanceOf[HOLFormula])
      val name = "\u039e("+ tri._1 +"_base, ("+cutConfToString( (ms11,ms22) ) + "))"
      ProjectionTermDB.put(name, tri._2)
      (name, PStructToExpressionTree(tri._2))
    })
    l
  }

  //for console printing
  def genCC(proof_name: String): List[(String, Tree[String], Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten
    val l = removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)
    l.map(pair => (pair._1, PStructToExpressionTree.applyConsole(extract(SchemaProofDB.get(pair._1).rec, pair._2._1.toSet ++ pair._2._2.toSet, getCutAncestors(SchemaProofDB.get(pair._1).rec))), (pair._2._1 ::: pair._2._1).toSet ))
  }

  //for ProofTool printing
  def genCCProofTool(proof_name: String): List[(String, ProjectionTerm, Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten
    val l = removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)
    l.map(pair => (pair._1, extract(SchemaProofDB.get(pair._1).rec, (pair._2._1 ::: pair._2._2).toSet, getCutAncestors(SchemaProofDB.get(pair._1).rec)), (pair._2._1 ::: pair._2._2).toSet ))
  }

  def genCCProofToolBase(proof_name: String): List[(String, ProjectionTerm, (Set[FormulaOccurrence], Set[FormulaOccurrence]))] = {
    val p_base = SchemaProofDB.get(proof_name).base
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(p_rec, pair._2._1 ::: pair._2._2, p_rec)).flatten
    println("\ncclist1 = "+cclist1)
    val cclistbase = removeDoubles(cclist1 ::: cclist).map(pair =>{
      val seq = SchemaProofDB.get(pair._1).base.root
      val k = IntVar("k")
      val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), IntZero().asInstanceOf[IntegerTerm] )
      var sub = SchemaSubstitution(new_map)
      val groundccant = pair._2._1.map(fo => sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])))
      val groundccsucc = pair._2._2.map(fo => sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])))
      val s = (seq.antecedent.filter(fo => groundccant.contains(fo.formula)), seq.succedent.filter(fo => groundccsucc.contains(fo.formula)))
      (pair._1, s)
    })
    removeDoubles(cclistbase).filter(pair =>
      pair._2._1.nonEmpty || pair._2._2.nonEmpty).map(pair =>
      (pair._1, extract(SchemaProofDB.get(pair._1).base, pair._2._1.toSet ++ pair._2._2.toSet, getCutAncestors(SchemaProofDB.get(pair._1).base)), (pair._2._1.toSet, pair._2._2.toSet) ))
  }

  //from cut occurrence configuration gives a cut configuration omega with (ant |- succ)
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
          new_map = Map.empty[SchemaVar, IntegerTerm] //+ Tuple2(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], index )
        else {
          val k = IntVar("k")
          new_map  = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, StepMinusOne.intTermPlus(k, len-1 ))
          sub = SchemaSubstitution(new_map)
          val newccAnt = seq1.antecedent.toList.filter(fo => foccsInSeqAnt.map(foo => foo.formula).contains(sub(fo.formula)))
          val newccSucc = seq1.succedent.toList.filter(fo => foccsInSeqSucc.map(foo => foo.formula).contains(sub(fo.formula)))
          return (proof_name, (newccAnt, newccSucc))::Nil
        }
      sub = SchemaSubstitution(new_map)
      val fccAnt = foccsInSeqAnt.map(fo => sub(fo.formula))
      val fccSucc = foccsInSeqSucc.map(fo => sub(fo.formula))
      val fcc = fccAnt ++ fccSucc
      (proof_name, (seq1.antecedent.filter(fo => fcc.contains(fo.formula)).toList, seq1.succedent.filter(fo => fcc.contains(fo.formula)).toList))::Nil
    }
    case Axiom(so) => List.empty[(String, (List[FormulaOccurrence], List[FormulaOccurrence]))]
    case UnaryTree(_,up) => getCC(up.asInstanceOf[LKProof], omega, p_old)
    case BinaryTree(_, up1, up2) => getCC(up1.asInstanceOf[LKProof], omega, p_old) ++ getCC(up2.asInstanceOf[LKProof], omega, p_old)
  }

  def apply(proof_name : String) = relevantProj(proof_name)
 
  def extract(pr: LKProof, omega: Set[FormulaOccurrence], cut_ancs: Set[FormulaOccurrence]): ProjectionTerm = {
    pr match {
      case Axiom(ro) => pAxiomTerm(ro)
      case WeakeningLeftRule(p, _, m) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), m.formula::Nil)
      }
      case SchemaProofLinkRule( seq0, link, index::_ ) => {
        pProofLinkTerm( seq0, omega, link, index.asInstanceOf[IntegerTerm], cut_ancs)
      }
      case WeakeningRightRule(p, _, m) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), m.formula::Nil)
      }
      case CutRule( p1, p2, _, a1, a2 ) => {
        val omega_ancs = getAncestors(omega)
        val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2 && !omega_ancs.contains(fo)),
          p2.root.succedent.filter(fo => !omega_ancs.contains(fo)))
        val w2 = Sequent(p1.root.antecedent.filter(fo => !omega_ancs.contains(fo)),
          p1.root.succedent.filter(fo => fo != a1 && !omega_ancs.contains(fo)))
        pPlus(p1.root, p2.root, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs), w1, w2)
      }
      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        val omega_ancs = getAncestors(omega)
        if (omega_ancs.contains(m) || cut_ancs.contains(m)) {
          val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)),
            p2.root.succedent.filter(fo => fo != a2 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)))
          val w2 = Sequent(p1.root.antecedent.filter(fo => fo != a1 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)),
            p1.root.succedent.filter(fo => fo != a1 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)))
          pPlus(p1.root, p2.root, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs), w1, w2)
        }
        else
          pTimes(pr.name, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs), a1.formula, a2.formula)
      }
      case AndRightRule(p1, p2, _, a1, a2, m) => {
        val omega_ancs = getAncestors(omega)
        if (omega_ancs.contains(m) || cut_ancs.contains(m)) {
          val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)),
            p2.root.succedent.filter(fo => fo != a2 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)))
          val w2 = Sequent(p1.root.antecedent.filter(fo => fo != a1 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)),
            p1.root.succedent.filter(fo => fo != a1 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)))
          pPlus(p1.root, p2.root, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs), w1, w2)
        }
        else
          pTimes(pr.name, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs), a1.formula, a2.formula)
      }
      case NegLeftRule( p, _, a, m ) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::Nil)
      }
      case AndLeft1Rule(p, r, a, m) =>  {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::m.formula::Nil)
      }
      case AndLeft2Rule(p, r, a, m) =>  {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::m.formula::Nil)
      }
      case OrRight1Rule(p, r, a, m) =>  {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::m.formula::Nil)
      }
      case OrRight2Rule(p, r, a, m) =>  {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::m.formula::Nil)
      }
      case NegRightRule( p, _, a, m ) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::Nil)
      }
      case ImpRightRule( p, _, a1, a2, m ) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a1.formula::a2.formula::Nil)
      }
      case ImpLeftRule(p1, p2, _, a1, a2, m) => {
        val omega_ancs = getAncestors(omega)
        if (omega_ancs.contains(m) || cut_ancs.contains(m)) {
          val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)),
            p2.root.succedent.filter(fo => fo != a2 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)))
          val w2 = Sequent(p1.root.antecedent.filter(fo => fo != a1 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)),
            p1.root.succedent.filter(fo => fo != a1 && !omega_ancs.contains(fo) && !cut_ancs.contains(fo)))
          pPlus(p1.root, p2.root, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs), w1, w2)
        }
        else
          pTimes(pr.name, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs), a1.formula, a2.formula)
      }
      case ContractionLeftRule(p, _, a1, a2, m) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a1.formula::a2.formula::Nil)
      }
      case ContractionRightRule(p, _, a1, a2, m) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a1.formula::a2.formula::Nil)
      }
      case ForallLeftRule( p, _, a, m, t ) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::m.formula::t::Nil)
      }
      case ForallRightRule( p, _, a, m, _ ) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          throw new Exception("\nProjection term can not be computed - the proof is not skolemized!\n")
      }
      case ExistsLeftRule( p, _, a, m, _ ) => {
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          throw new Exception("\nProjection term can not be computed - the proof is not skolemized!\n")
      }
      case ExistsRightRule( p, _, a, m, t ) => 
        if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
          extract(p, omega, cut_ancs)
        else
          pUnary(pr.name, extract(p, omega, cut_ancs), a.formula::m.formula::t::Nil)
      
      case AndEquivalenceRule1(up, r, aux, main) =>  extract(up, omega, cut_ancs)
      
      case AndEquivalenceRule2(up, r, aux, main) =>  extract(up, omega, cut_ancs)
      
      case AndEquivalenceRule3(up, r, aux, main) =>  extract(up, omega, cut_ancs)
      
      case OrEquivalenceRule1(up, r, aux, main) =>  extract(up, omega, cut_ancs)
      
      case OrEquivalenceRule2(up, r, aux, main) =>  extract(up, omega, cut_ancs)
      
      case OrEquivalenceRule3(up, r, aux, main) =>  extract(up, omega, cut_ancs)
      
      case trsArrowLeftRule( p, _, a, m ) => extract(p, omega, cut_ancs)
      
      case trsArrowRightRule( p, _, a, m ) => extract(p, omega, cut_ancs)

      case _ => { println("ERROR in extraction of projection term : missing rule! "+pr.rule);throw new Exception("ERROR in extract: ProjectionTermCreators "+pr.rule) }
    }
  }
}



object PStructToExpressionTree {

  def apply(s: ProjectionTerm) : Tree[AnyRef] = s match {
    case pTimes(rho, left, right, aux1, aux2) => BinaryTree(new PTimesC(rho), apply(left), apply(right))
    case pPlus(seq1, seq2, left, right, w1, w2) => {
      val t1 = if (w1.antecedent.isEmpty && w1.succedent.isEmpty) apply(left)
               else UnaryTree(new PWeakC(w1), apply(left))
      val t2 = if (w2.antecedent.isEmpty && w2.succedent.isEmpty) apply(right)
               else UnaryTree(new PWeakC(w2), apply(right))
      BinaryTree(PPlusC, t1, t2)

    }
    case pUnary(rho, upper, auxl) => UnaryTree(rho, apply(upper))
    case pAxiomTerm(seq) => {
      LeafTree(seq)
    }
    case pProofLinkTerm( seq, omega, proof_name, index, canc ) => {
      val cut_omega_anc = canc ++ getAncestors(omega)
      val seq1 = SchemaProofDB.get(proof_name).rec.root
      val len = StepMinusOne.lengthVar(index)
      val foccsInSeqAnt = seq.antecedent.filter(fo => cut_omega_anc.contains(fo))
      val foccsInSeqSucc = seq.succedent.filter(fo => cut_omega_anc.contains(fo))
      var new_map = Map.empty[SchemaVar, IntegerTerm]
      var strant = "";var str1ant = "";var strsucc = "";var str1succ = "";
      val k = IntVar("k")
      val trans_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, IntVar("n") )
      val trans_sub = SchemaSubstitution(trans_map)
      var f1 = Seq.empty[HOLExpression];var f2 = Seq.empty[HOLExpression];
      if (len == 0) {
        f1 = foccsInSeqAnt.map(fo => trans_sub(fo.formula.asInstanceOf[SchemaFormula]))
        f2 = foccsInSeqSucc.map(fo => trans_sub(fo.formula.asInstanceOf[SchemaFormula]))
      }
      else {
        f1 = foccsInSeqAnt.map(fo => trans_sub(StepMinusOne.minusMore(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar], len)))
        f2 = foccsInSeqSucc.map(fo => trans_sub(StepMinusOne.minusMore(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar], len)))
      }
      val ms = new Multisets.HashMultiset[HOLFormula](HashMap.empty[HOLFormula, Int])
      val ms11 = f1.foldLeft(ms)((res,f) => res + f.asInstanceOf[HOLFormula])
      val ms22 = f2.foldLeft(ms)((res,f) => res + f.asInstanceOf[HOLFormula])
      LeafTree(IndexedPredicate(new ProjectionSetSymbol(proof_name, (ms11,ms22)), index::Nil))
    }
  }


// for nice printing in console - the braces are with different colors and such things
  def applyConsole(s: ProjectionTerm) : Tree[String] = s match {

    case pTimes(rho, left, right, a1, a2) => BinaryTree[String]((new PTimesC("")).toString + rho, applyConsole(left), applyConsole(right))
    case pPlus(seq1, seq2, left, right, w1, w2) => {
      val t1 = UnaryTree[String]("w^{"+ printSchemaProof.sequentToString(w1) +"}", applyConsole(left))
      val t2 = UnaryTree[String]("w^{"+ printSchemaProof.sequentToString(w2) +"}", applyConsole(right))
      BinaryTree[String]((PPlusC).toString, t1, t2)
    }
    case pUnary(rho, upper, l) => UnaryTree[String](rho, applyConsole(upper))
    case pAxiomTerm(seq) => {
      LeafTree[String](printSchemaProof.sequentToString(seq))
    }
    case pProofLinkTerm( seq, omega, proof_name, index, ccanc ) => {
      val cut_omega_anc = ccanc ++ getAncestors(omega)
      val seq1 = SchemaProofDB.get(proof_name).rec.root
      val k = IntVar("k")
      val len = StepMinusOne.length(index, k)
      val foccsInSeqAnt = seq.antecedent.filter(fo => cut_omega_anc.contains(fo))
      val foccsInSeqSucc = seq.succedent.filter(fo => cut_omega_anc.contains(fo))
      var new_map = Map.empty[SchemaVar, IntegerTerm]
      var strant = "";var str1ant = "";var strsucc = "";var str1succ = "";
      val trans_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, IntVar("n") )
      val trans_sub = SchemaSubstitution(trans_map)
      var f1 = Seq.empty[HOLExpression];var f2 = Seq.empty[HOLExpression];
      if (len == 0) {
          f1 = foccsInSeqAnt.map(fo => trans_sub(fo.formula.asInstanceOf[SchemaFormula]))
          f2 = foccsInSeqSucc.map(fo => trans_sub(fo.formula.asInstanceOf[SchemaFormula]))
      }
      else {
        f1 = foccsInSeqAnt.map(fo => trans_sub(StepMinusOne.minusMore(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar], len)))
        f2 = foccsInSeqSucc.map(fo => trans_sub(StepMinusOne.minusMore(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar], len)))
      }
      if (f1.size == 0)
        strant = ""
      else if (f1.size == 1)
        str1ant = f1.head.toString
      else
        str1ant = f1.tail.foldLeft(", ")((res,f) => f.toString + res)
      if (f2.size == 0)
        strsucc = ""
      else if (f2.size == 1)
        str1succ = f2.head.toString
      else
        str1succ = f2.tail.foldLeft(", ")((res,f) => f.toString+res)
      return LeafTree[String]("pr^"+Console.RESET+"{"+Console.CYAN+strant+str1ant+"|"+strsucc+str1succ +Console.RESET+"},"+proof_name+"("+Console.MAGENTA+Console.UNDERLINED+index.toString+Console.RESET+")")
    }
  }


  // We define some symbols that represent the operations of the struct
 case class PTimesSymbol(val rho: String) extends LogicalSymbolA {
    override def unique = "TimesSymbol"
    override def toString = "⊗_"+rho
    def toCode = "TimesSymbol"
  }

  case object PPlusSymbol extends LogicalSymbolA {
    override def unique = "PlusSymbol"
    override def toString = "⊕"
    def toCode = "PlusSymbol"
  }

  case class PWeakSymbol(val seq: Sequent) extends LogicalSymbolA {
    override def unique = "WeakSymbol"
    override def toString = "w^{"+seq.toString+"}"
    def toCode = "WeakSymbol"
  }

  class ProjectionSetSymbol (val name: String, val cut_occs: (Multiset[HOLFormula], Multiset[HOLFormula])) extends SymbolA {
    override def toString() =
      "pr^{(" + cutConfToString(cut_occs) + ")," + name +"}"
  }

  case class PTimesC(val rho: String) extends HOLConst(new PTimesSymbol(rho), Type("( o -> (o -> o) )"))
  case object PPlusC extends HOLConst(PPlusSymbol, Type("( o -> (o -> o) )"))
  case class PWeakC(val seq: Sequent) extends HOLConst(new PWeakSymbol(seq), Type("(o -> o)"))


  // for nice printing in Console only !
  def printTree(r: Tree[String]): Unit = r match {
    case LeafTree(vert) => print(" "+Console.MAGENTA+Console.UNDERLINED+vert+Console.RESET+" ")

    case UnaryTree(vert, up) => {
      if (vert.startsWith("w"))
        print(Console.YELLOW )
      else
        print(Console.GREEN )
      print(" "+vert)
      print(Console.RESET)
      printTree(up.asInstanceOf[Tree[String]])
    }

    case BinaryTree(vert, up1, up2) => {
      if (vert == PPlusSymbol.toString)
        print(Console.BLUE)
      else
        print(Console.RED)
      print("(")
      print(Console.RESET)
      printTree(up1.asInstanceOf[Tree[String]])
      if (vert == PPlusSymbol.toString) {
        print(Console.BLUE)
        print("\n\n                                   "+vert+"\n\n")
      }
      else {
        print(Console.RED)
        print(" "+vert+" ")
      }

      print(Console.RESET)
      printTree(up2.asInstanceOf[Tree[String]])
      if (vert == PPlusSymbol.toString)
        print(Console.BLUE)
      else
        print(Console.RED)
      print(")")
      print(Console.RESET)
    }
    case _ => throw new Exception("Error in printTree, ProjectionTerm.scala")
  }
}

// returns a ground projection term for a given instance of the parameter k
  object GroundingProjectionTerm {
    def apply(pair: Tuple2[ProjectionTerm,ProjectionTerm], i: Int): ProjectionTerm = {
      val k = IntVar("k")
      if(i < 0)
        throw new Exception("\n\nThe instance for computing projections is not a natural number !\n")
      if(i == 0) {
        val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), IntZero() )
        val subst = SchemaSubstitution(new_map)
        apply(pair._1, subst)
      }
      else {
        val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), toIntegerTerm(i-1))
        val subst = SchemaSubstitution(new_map)
        apply(pair._2, subst)
      }
    }

    def apply(t: ProjectionTerm, subst: SchemaSubstitution): ProjectionTerm = {
      t match {
        case times: pTimes => {
          val left = GroundingProjectionTerm(times.left, subst)
          val right = GroundingProjectionTerm(times.right, subst)
          pTimes(times.rho, left, right, subst(times.aux1.asInstanceOf[SchemaFormula]), subst(times.aux2.asInstanceOf[SchemaFormula]))
        }
        case plus: pPlus => {
          val left = GroundingProjectionTerm(plus.left, subst)
          val right = GroundingProjectionTerm(plus.right, subst)
          val ant1 = plus.seq1.antecedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          val succ1 = plus.seq1.succedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          val ant2 = plus.seq2.antecedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          val succ2 = plus.seq2.succedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          //w1 and w2
          val want1 = plus.w1.antecedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          val wsucc1 = plus.w1.succedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          val want2 = plus.w2.antecedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          val wsucc2 = plus.w2.succedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          pPlus(Sequent(ant1, succ1), Sequent(ant2, succ2), left, right, Sequent(want1, wsucc1), Sequent(want2, wsucc2))
        }
        case unary: pUnary => {
          pUnary(unary.rho, GroundingProjectionTerm(unary.upper, subst), unary.auxl.map(f => subst(f.asInstanceOf[SchemaFormula])))
        }
        case pProofLinkTerm( seq, omega, proof_name, index, canc ) => {
          pProofLinkTerm( seq, omega, proof_name, subst(index).asInstanceOf[IntegerTerm], canc )
        }

        case ax: pAxiomTerm => {
          val ant = ax.seq.antecedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          val succ = ax.seq.succedent.map(x => {x.factory.createFormulaOccurrence(subst(x.formula.asInstanceOf[SchemaFormula]), Nil)})
          pAxiomTerm(Sequent(ant, succ))
        }
      }
    }
  }

object ProjectionTermDB extends Iterable[(String, ProjectionTerm)] with TraversableOnce[(String, ProjectionTerm)] {
  val terms = new scala.collection.mutable.HashMap[String, ProjectionTerm]
  def clear = terms.clear
  def get(name: String) = terms(name)
  def put(name: String, term: ProjectionTerm) = terms.put(name, term)
  def iterator = terms.iterator
}

//unfolds (normalizes) a projection term, i.e. removes the "pr" symbols according to the rewriting rules (see the journal paper)
  object UnfoldProjectionTerm {
    // This method is used in ProofTool.
    // It should return unfolded term as a tree and the list of projections
    def apply(name: String, number: Int): (Tree[_], List[(String,LKProof)]) = {
      val gr = GroundingProjectionTerm((ProjectionTermDB.get(name.replace("step", "base")),ProjectionTermDB.get(name.replace("base", "step"))),number)
      val pt = RemoveArrowRules(UnfoldProjectionTerm(gr))
      val tree = PStructToExpressionTree(pt)
      val l = ProjectionTermToSetOfProofs(pt).toList
      val proof_name = name.replace("Ξ(","").replace("_base","\n").replace("_step","\n").takeWhile(c => !c.equals('\n'))
      val fl = filterProjectionSet(l,getEndSequent(proof_name, number))
      val list = fl.map(p => (proof_name + "↓" + number + "_proj_" + fl.indexOf(p),p))
      (tree,list)
    }

  // Maybe this function can be used also in other places???
    def getEndSequent(proof: String, number: Int): FSequent = {
      val k = IntVar("k")
      val seq = SchemaProofDB.get(proof).seq
      val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(k, toIntegerTerm(number))
      val sub = SchemaSubstitution(new_map)
      FSequent(seq.antecedent.map(f => unfoldSFormula(sub(f.asInstanceOf[SchemaFormula]))), seq.succedent.map(f => unfoldSFormula(sub(f.asInstanceOf[SchemaFormula]))))
    }

    def filterProjectionSet(proofs: List[LKProof], end_seq: FSequent): List[LKProof] = proofs.filter(proof => {
      val proj_end_seq = proof.root.toFSequent
      proj_end_seq.antecedent.diff(end_seq.antecedent).intersect(proj_end_seq.succedent.diff(end_seq.succedent)).isEmpty
    })

    def apply(t: ProjectionTerm): ProjectionTerm = {
      t match {
        case pProofLinkTerm( seq0, omega, proof_name, index, canc ) => {

          if(index == IntZero()) {
            val p = SchemaProofDB.get(proof_name).base
            val seq = p.root
            val k = IntVar("k")
            val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), IntZero().asInstanceOf[IntegerTerm] )
            var sub = SchemaSubstitution(new_map)
            val omega_sub = omega.map(fo => sub(StepMinusOne.minusOne(fo.formula.asInstanceOf[SchemaFormula], k.asInstanceOf[IntVar])))
            val omega1 = (seq.antecedent ++ seq.succedent).toSet.filter(fo => omega_sub.contains(fo.formula.asInstanceOf[SchemaFormula]))
            val omega1Anc = omega1.foldLeft(Set.empty[FormulaOccurrence])((acc, fo)=> acc ++ getAncestors(fo))
            return ProjectionTermCreators.extract(p, omega1, omega1Anc)
          }
          val p = SchemaProofDB.get(proof_name).rec
          val seq = p.root
          val k = IntVar("k")
          val omega1 = (seq0.antecedent ++ seq0.succedent).toSet.filter(fo => canc.contains(fo) || getAncestors(omega).contains(fo))


          val omega1ant = seq0.antecedent.toSet.filter(fo => canc.contains(fo) || getAncestors(omega).contains(fo))
          val omega1succ = seq0.succedent.toSet.filter(fo => canc.contains(fo) || getAncestors(omega).contains(fo))
          val mapFind = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Succ(k.asInstanceOf[IntegerTerm]).asInstanceOf[IntegerTerm] )
          var subFind = SchemaSubstitution(mapFind)
          /*next lines are related with the index of the proof-link.
            We have to map the configuration in the proof-link to the
            corresponding occurrences in the end-sequent.
            The proof-links are of the form (φ,k+1) or (φ,k).
            When the term is grounded this is not immediately visible.
           */
          val b = omega1ant.forall(fo => seq.antecedent.map(fo =>fo.formula).contains(subFind(fo.formula.asInstanceOf[SchemaFormula]))) && omega1succ.forall(fo => seq.succedent.map(fo =>fo.formula).contains(subFind(fo.formula.asInstanceOf[SchemaFormula])))
          val new_map1 = b match {
            case false => Map.empty[SchemaVar, IntegerTerm]
            case true => Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Succ(k.asInstanceOf[IntegerTerm]).asInstanceOf[IntegerTerm] )
          }
          var sub1 = SchemaSubstitution(new_map1)
          val omega1_sub = omega1.map(fo => sub1(fo.formula.asInstanceOf[SchemaFormula]))
          val endSeqOcc = (seq.antecedent ++ seq.succedent).toSet.filter(fo => omega1_sub.contains(fo.formula.asInstanceOf[SchemaFormula])) ++ getAncestors(omega)
          val omega1Anc = endSeqOcc.foldLeft(Set.empty[FormulaOccurrence])((acc, fo)=> acc ++ getAncestors(fo))
          val pterm = ProjectionTermCreators.extract(p, endSeqOcc, omega1Anc ++ getCutAncestors(p))
          val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Pred(index) )
          var sub = SchemaSubstitution(new_map)
          val ground = GroundingProjectionTerm(pterm, sub)
          UnfoldProjectionTerm(ground)
        }
        case times: pTimes => {
          val left = UnfoldProjectionTerm(times.left)
          val right = UnfoldProjectionTerm(times.right)
          pTimes(times.rho, left, right, times.aux1, times.aux2)
        }
        case plus: pPlus => {
          val left = UnfoldProjectionTerm(plus.left)
          val right = UnfoldProjectionTerm(plus.right)
          pPlus(plus.seq1, plus.seq2, left, right, plus.w1, plus.w2)
        }
        case unary: pUnary => pUnary(unary.rho, UnfoldProjectionTerm(unary.upper), unary.auxl)
        case ax: pAxiomTerm => ax
        case _ => throw new Exception("\n\nERROR in UnfoldProjectionTerm !\n")
      }
    }
  }

//creates a set of proof projections from an unfolded (normalized) projection term
  object ProjectionTermToSetOfProofs {
    private def WeakLeftRight(p: LKProof, seq: Sequent): LKProof = {
      val p1 = seq.antecedent.foldLeft(p)((res, fo) => WeakeningLeftRule(res, fo.formula))
      seq.succedent.foldLeft(p1)((res, fo) => WeakeningRightRule(res, fo.formula))
    }

    def apply(t: ProjectionTerm): Set[LKProof] = {
      t match {
        case ax: pAxiomTerm => Set.empty[LKProof] + Axiom(ax.seq)
        case plus: pPlus => {
          val s1 = ProjectionTermToSetOfProofs(plus.left)
          val s2 = ProjectionTermToSetOfProofs(plus.right)
          s1.map(p => WeakLeftRight(p, plus.w1)) ++ s2.map(p => WeakLeftRight(p, plus.w2))
        }
        case unary: pUnary => {
          val set = ProjectionTermToSetOfProofs(unary.upper)
          unary.rho match {
            case "w:l" => set.map(p => WeakeningLeftRule(p, unary.auxl.head.asInstanceOf[HOLFormula]))
            case "w:r" => set.map(p => WeakeningRightRule(p, unary.auxl.head.asInstanceOf[HOLFormula]))
            case "c:l" => set.map(p => ContractionLeftRule(p, unary.auxl.head.asInstanceOf[HOLFormula]))
            case "c:r" => set.map(p => ContractionRightRule(p, unary.auxl.head.asInstanceOf[HOLFormula]))
            case "\u00ac:l" => set.map(p => NegLeftRule(p, unary.auxl.head.asInstanceOf[HOLFormula]))
            case "\u00ac:r" => set.map(p => NegRightRule(p, unary.auxl.head.asInstanceOf[HOLFormula]))
            case "\u2200:l" => set.map(p => ForallLeftRule(p, unary.auxl.head.asInstanceOf[HOLFormula], unary.auxl.tail.head.asInstanceOf[HOLFormula], unary.auxl.last))
            case "\u2203:r" => set.map(p => ExistsRightRule(p, unary.auxl.head.asInstanceOf[HOLFormula], unary.auxl.tail.head.asInstanceOf[HOLFormula], unary.auxl.last))
            case "\u2283:r" => set.map(p => ImpRightRule(p, unary.auxl.head.asInstanceOf[HOLFormula], unary.auxl.last.asInstanceOf[HOLFormula]))
            case "\u2227:l1" => {
              val a = unary.auxl.last match {
                case And(f1, f2) => f1.asInstanceOf[HOLFormula]
              }
              set.map(p => AndLeft1Rule(p, a, unary.auxl.head.asInstanceOf[HOLFormula]))
            }
            case "\u2227:l2" => {
              val a = unary.auxl.last match {
                case And(f1, f2) => f2.asInstanceOf[HOLFormula]
              }
              set.map(p => AndLeft2Rule(p, a, unary.auxl.head.asInstanceOf[HOLFormula]))
            }
            case "\u2228:r1" => {
              val a = unary.auxl.last match {
                case Or(f1, f2) => f1.asInstanceOf[HOLFormula]
              }
              set.map(p => OrRight1Rule(p, a, unary.auxl.head.asInstanceOf[HOLFormula]))
            }
            case "\u2228:r2" => {
              val a = unary.auxl.last match {
                case Or(f1, f2) => f2.asInstanceOf[HOLFormula]
              }
              set.map(p => OrRight2Rule(p, a, unary.auxl.head.asInstanceOf[HOLFormula]))
            }
            case "\u21A0:l" => set.map(p => trsArrowLeftRule(p, unary.auxl.head.asInstanceOf[SchemaFormula], unary.auxl.last.asInstanceOf[SchemaFormula]))
            case "\u21A0:r" => set.map(p => trsArrowRightRule(p, unary.auxl.head.asInstanceOf[SchemaFormula], unary.auxl.last.asInstanceOf[SchemaFormula]))
            case _ => throw new Exception("\n\nmissing case in pUnary in ProjectionTermToSetOfProofs !\n\n")
          }
        }
        case times: pTimes => {
          val s1 = ProjectionTermToSetOfProofs(times.left)
          val s2 = ProjectionTermToSetOfProofs(times.right)
          //cartesian product
          val S1xS2 = s1.map(x => s2.map(y => (x, y))).flatten
          times.rho match {
            case "\u2283:l" => S1xS2.map(pair => ImpLeftRule(pair._1, pair._2, times.aux1, times.aux2))
            case "\u2228:l" => S1xS2.map(pair => OrLeftRule(pair._1, pair._2, times.aux1, times.aux2))
            case "\u2227:r" => S1xS2.map(pair => AndRightRule(pair._1, pair._2, times.aux1, times.aux2))
            case _ => throw new Exception("\n\n missing case in times in ProjectionTermToSetOfProofs !\n\n")
          }
        }
        case _ => throw new Exception("\n\nThe projection term is not normalized/unfolded !\n\n")
      }
    }
  }

  
  //removes the ↠:l and ↠:r inferences, i.e. normalizes the formulas in term level
  object RemoveArrowRules {
    private def NormalizeSequent(seq: Sequent): Sequent = {
      Sequent(seq.antecedent.map(fo => fo.factory.createFormulaOccurrence(unfoldSFormula(fo.formula.asInstanceOf[SchemaFormula]), Nil)), seq.succedent.map(fo => fo.factory.createFormulaOccurrence(unfoldSFormula(fo.formula.asInstanceOf[SchemaFormula]), Nil)))
    }
    def apply(t: ProjectionTerm): ProjectionTerm = {
      t match {
        case ax: pAxiomTerm => pAxiomTerm(NormalizeSequent(ax.seq))
        case times: pTimes => {
          val left = RemoveArrowRules(times.left)
          val right = RemoveArrowRules(times.right)
          pTimes(times.rho, left, right, unfoldSFormula(times.aux1.asInstanceOf[SchemaFormula]), unfoldSFormula(times.aux2.asInstanceOf[SchemaFormula]))
        }
        case plus: pPlus => {
          val left = RemoveArrowRules(plus.left)
          val right = RemoveArrowRules(plus.right)
          pPlus(NormalizeSequent(plus.seq1), NormalizeSequent(plus.seq2), left, right, NormalizeSequent(plus.w1), NormalizeSequent(plus.w2))
        }
        case unary: pUnary => unary.rho match {
          case "\u21A0:l" => RemoveArrowRules(unary.upper)
          case "\u21A0:r" => RemoveArrowRules(unary.upper)
          case _ => pUnary(unary.rho, RemoveArrowRules(unary.upper),
            if (unary.auxl.length < 3)
              unary.auxl.map(t => unfoldSFormula(t.asInstanceOf[SchemaFormula]))
            else
              unfoldSFormula(unary.auxl.head.asInstanceOf[SchemaFormula])::unfoldSFormula(unary.auxl.tail.head.asInstanceOf[SchemaFormula]):: {
                unary.auxl.last match {
                  case sIndTerm(_, _) => unfoldSINDTerm(unary.auxl.last.asInstanceOf[SchemaFormula])
                  case sTerm(_, _, _) => unfoldSTerm(unary.auxl.last.asInstanceOf[SchemaFormula])
                  case _ => unary.auxl.last
                }
              }::Nil)
        }
        case _ => throw new Exception("\n\nERROR in UnfoldProjectionTerm !\n")
      }
    }
  }
