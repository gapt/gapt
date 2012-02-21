package at.logic.transformations.ceres

import at.logic.calculi.lk.lkExtractors.{BinaryLKProof, UnaryLKProof}
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.fol.Utils
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, LogicalSymbolsA}
import at.logic.language.lambda.symbols.{SymbolA, VariableStringSymbol}
import at.logic.transformations.ceres.PStructToExpressionTree._
import at.logic.utils.ds.Multisets
import at.logic.utils.ds.Multisets.Multiset
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.hol.{HOLConst, HOLExpression, HOLFormula}
import at.logic.utils.ds.trees.{BinaryTree, UnaryTree, LeafTree, Tree}
import at.logic.algorithms.lk.{getCutAncestors, getAncestors}
import at.logic.calculi.slk._
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{defaultFormulaOccurrenceFactory, FormulaOccurrence}
import at.logic.language.schema._
import at.logic.calculi.proofs.{BinaryRuleTypeA, UnaryRuleTypeA, NullaryRuleTypeA}
import projections.printSchemaProof
import collection.immutable.HashMap
import struct.{cutOccConfigToCutConfig, StructCreators, TypeSynonyms}

//import scala.collection.mutable.{Map, HashMap}
import unfolding.{StepMinusOne, SchemaSubstitution1}


//import struct._
import at.logic.language.lambda.types.ImplicitConverters._

trait ProjectionTerm

class pTimes(val rho: String, val left: ProjectionTerm, val right: ProjectionTerm) extends ProjectionTerm
class pPlus(val seq1: Sequent, val seq2: Sequent, val left: ProjectionTerm, val right: ProjectionTerm, val w1: Sequent, val w2: Sequent) extends ProjectionTerm
class pUnary(val rho: String, val upper: ProjectionTerm) extends ProjectionTerm
class pProofLinkTerm(val seq: Sequent, val omega: Set[FormulaOccurrence], val proof_name: String, val index: IntegerTerm, val ccanc: Set[FormulaOccurrence]) extends ProjectionTerm
class pAxiomTerm(val seq: Sequent) extends ProjectionTerm


object pTimes {
  def apply(rho: String, left: ProjectionTerm, right: ProjectionTerm) : pTimes = {
    new pTimes(rho, left, right)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t : pTimes => Some((t.rho, t.left, t.right))
    case _ => None
  }
}

object pPlus {
  def apply(seq1: Sequent, seq2: Sequent, left: ProjectionTerm, right: ProjectionTerm, w1: Sequent, w2: Sequent): pPlus = {
    new pPlus(seq1, seq2, left, right, w1, w2)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t : pPlus => Some((t.seq1, t.seq2, t.left, t.right, t.w1, t.w2))
    case _ => None
  }
}

object pUnary {
  def apply(rho: String, upper: ProjectionTerm) = {
    new pUnary(rho, upper)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t : pUnary => Some((t.rho, t.upper))
    case _ => None
  }
}

object pProofLinkTerm {
  def apply(seq: Sequent, omega: Set[FormulaOccurrence], proof_name: String, index: IntegerTerm, ccanc: Set[FormulaOccurrence]) = {
    new pProofLinkTerm(seq, omega, proof_name, index, ccanc)

  }
  def unapply(term : ProjectionTerm) = term match {
    case t: pProofLinkTerm => Some((t.seq, t.omega, t.proof_name, t.index, t.ccanc))
    case _ => None
  }
}

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
    val spt = SchemaProofDB.toList.map(pair => genCCProofTool(pair._1))
    val sptb = SchemaProofDB.toList.map(pair => genCCProofToolBase(pair._1))

    val sl    = (main_proof, PStructToExpressionTree.applyConsole(extract(SchemaProofDB.get(main_proof).rec, Set.empty[FormulaOccurrence], getCutAncestors(SchemaProofDB.get(main_proof).rec))), Set.empty[FormulaOccurrence]) :: s.flatten //for console
    val slpt  = (main_proof, PStructToExpressionTree(extract(SchemaProofDB.get(main_proof).rec,  Set.empty[FormulaOccurrence], getCutAncestors(SchemaProofDB.get(main_proof).rec))) , Set.empty[FormulaOccurrence]) :: spt.flatten
    val slptb = (main_proof, PStructToExpressionTree(extract(SchemaProofDB.get(main_proof).base, Set.empty[FormulaOccurrence], getCutAncestors(SchemaProofDB.get(main_proof).base))), (Set.empty[FormulaOccurrence], Set.empty[FormulaOccurrence])) :: sptb.flatten
//    println("\n\n\n"+slptb.size)
//    slptb.foreach(tri => { println("\n"+tri._1); tri._3.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))})

    val l  = slpt.map(tri => {
      val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
      val trans_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(k, IntVar(new VariableStringSymbol("n")) )
      val trans_sub = new SchemaSubstitution1[HOLExpression](trans_map)
      val seq = SchemaProofDB.get(tri._1).rec.root
      val ms1 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms2 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms11 = tri._3.filter(fo => seq.antecedent.contains(fo)).map(fo => trans_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar]))).foldLeft(ms1)((res,f) => res + f.asInstanceOf[SchemaFormula])
      val ms22 = tri._3.filter(fo => seq.succedent.contains(fo)).map(fo => trans_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar]))).foldLeft(ms1)((res,f) => res + f.asInstanceOf[SchemaFormula])
//      println("\nslpt\n")
//      ms11.foreach(f => println(printSchemaProof.formulaToString(f)))
//      print("\n\n\n")
//      ms22.foreach(f => println(printSchemaProof.formulaToString(f)))
//      print("\n\n\n")
      ("\u039e("+ tri._1 +"_step, ("+cutConfToString( (ms11,ms22) ) + "))", tri._2)
    }) ::: slptb.map(tri => {
      val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
      val trans1_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(k, IntVar(new VariableStringSymbol("n")) )
      val trans1_sub = new SchemaSubstitution1[HOLExpression](trans1_map)
      val trans_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(k, IntZero() )
      val trans_sub = new SchemaSubstitution1[HOLExpression](trans_map)
      val seq = SchemaProofDB.get(tri._1).rec.root
      val ms1 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms2 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms11 = seq.antecedent.filter(fo => tri._3._2.map(x => x.formula).contains(trans_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])).asInstanceOf[HOLFormula])).foldLeft(ms1)((res,fo) => res + trans1_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])).asInstanceOf[SchemaFormula])
      val ms22 =  seq.succedent.filter(fo => tri._3._2.map(x => x.formula).contains(trans_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])).asInstanceOf[HOLFormula])).foldLeft(ms2)((res,fo) => res + trans1_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])).asInstanceOf[SchemaFormula])
//      val ms11 = tri._3.filter(fo => seq.antecedent.contains(fo)).map(fo => trans_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar]))).foldLeft(ms1)((res,f) => res + f.asInstanceOf[SchemaFormula])
//      val ms22 = tri._3.filter(fo => seq.succedent.contains(fo)).map(fo => trans_sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar]))).foldLeft(ms1)((res,f) => res + f.asInstanceOf[SchemaFormula])
//      println("\nslpt\n")
//      ms11.foreach(f => println(printSchemaProof.formulaToString(f)))
//      print("\n\n\n")
//      ms22.foreach(f => println(printSchemaProof.formulaToString(f)))
//      print("\n\n\n")
      ("\u039e("+ tri._1 +"_base, ("+cutConfToString( (ms11,ms22) ) + "))", tri._2)
    })
    println("l.size = "+l.size)
    l.foreach(x => println(x._1))
    l
  }

  def apply(proof_name : String) = relevantProj(proof_name)

  // Takes all proofs from SchemaProofDB and computes projections for all cut-configurations
  def apply() : List[(String,Tree[_])] = {
    var projs = List[(String,Tree[_])]()
    SchemaProofDB.foreach( pair => {
      val cutConfs_base = StructCreators.cutConfigurations(pair._2.base)
      val set_base = cutConfs_base.map( cc => ("\u039e(" + pair._1 + "_base, (" +
        cutConfToString( cutOccConfigToCutConfig( pair._2.base.root, cc, pair._2.seq, pair._2.vars, IntZero()::Nil ) ) + "))",
        PStructToExpressionTree(extract( pair._2.base, cc, getCutAncestors(pair._2.base))))).toList
      val cutConfs_step = StructCreators.cutConfigurations(pair._2.rec)
      val set_step = cutConfs_step.map( cc => ("\u039e(" + pair._1 + "_step, (" +
        cutConfToString( cutOccConfigToCutConfig( pair._2.rec.root, cc, pair._2.seq, pair._2.vars,  Succ(IntVar(new VariableStringSymbol("k") ))::Nil ) ) + "))",
        PStructToExpressionTree(extract( pair._2.rec, cc, getCutAncestors(pair._2.rec))))).toList
      projs = projs ::: set_base ::: set_step
    } )
    projs
  }

  def cutConfToString( cc : TypeSynonyms.CutConfiguration ) = {
    def str( m : Multiset[SchemaFormula] ) = m.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + printSchemaProof.formulaToString(f) )
    str( cc._1 ) + " | " + str( cc._2 )
  }

  //for console printing
  def genCC(proof_name: String): List[(String, Tree[String], Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten

    val l = Utils.removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)

    l.foreach(pair => {
      println("\n\n\n"+pair._1 +" : ")
      pair._2._1.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
      pair._2._2.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    })

    l.map(pair => (pair._1,
                   PStructToExpressionTree.applyConsole(extract(SchemaProofDB.get(pair._1).rec, pair._2._1.toSet ++ pair._2._2.toSet, getCutAncestors(SchemaProofDB.get(pair._1).rec))),
                   (pair._2._1 ::: pair._2._1).toSet ))
  }

  //for ProofTool printing
  def genCCProofTool(proof_name: String): List[(String, Tree[AnyRef], Set[FormulaOccurrence])] = {
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(SchemaProofDB.get(pair._1).rec, pair._2._1 ::: pair._2._2, SchemaProofDB.get(pair._1).rec)).flatten
    val l = Utils.removeDoubles(cclist ::: cclist1).filter(pair => pair._2._1.nonEmpty || pair._2._2.nonEmpty)
    l.foreach(tri => {
      println("\n"+tri._1)
      tri._2._1.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
      tri._2._2.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    })
    l.map(pair => (pair._1, PStructToExpressionTree(extract(SchemaProofDB.get(pair._1).rec, (pair._2._1 ::: pair._2._2).toSet, getCutAncestors(SchemaProofDB.get(pair._1).rec))), (pair._2._1 ::: pair._2._2).toSet ))
  }

  def genCCProofToolBase(proof_name: String): List[(String, Tree[AnyRef], (Set[FormulaOccurrence], Set[FormulaOccurrence]))] = {
    val p_base = SchemaProofDB.get(proof_name).base
    val p_rec = SchemaProofDB.get(proof_name).rec
    val cclist = getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    val cclistproof_name = cclist.filter(pair => pair._1 == proof_name)
    val cclist1 = cclistproof_name.map(pair => getCC(p_rec, pair._2._1 ::: pair._2._2, p_rec)).flatten

    val cclistbase = (cclist1 ::: cclist).map(pair =>{
      val seq = SchemaProofDB.get(pair._1).base.root
      val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
      val new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], IntZero().asInstanceOf[IntegerTerm] )
      var sub = new SchemaSubstitution1[HOLExpression](new_map)
      val groundccant = pair._2._1.map(fo => sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])))
      val groundccsucc = pair._2._2.map(fo => sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])))
      val s = (seq.antecedent.filter(fo => groundccant.contains(fo.formula)), seq.succedent.filter(fo => groundccsucc.contains(fo.formula)))

      (pair._1, s)
    })
//    cclistbase.foreach(pair => {
//      println("\n\n"+pair._1)
//      pair._2._1.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
//      pair._2._2.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
//    })
    Utils.removeDoubles(cclistbase).filter(pair =>
      pair._2._1.nonEmpty || pair._2._2.nonEmpty).map(pair =>
      (pair._1, PStructToExpressionTree(extract(SchemaProofDB.get(pair._1).base, pair._2._1.toSet ++ pair._2._2.toSet, getCutAncestors(SchemaProofDB.get(pair._1).base))), (pair._2._1.toSet, pair._2._2.toSet) ))
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


  def extract(pr: LKProof, omega: Set[FormulaOccurrence], cut_ancs: Set[FormulaOccurrence]): ProjectionTerm = pr match {
    case Axiom(ro) => pAxiomTerm(ro)
    case WeakeningLeftRule(p, _, m) => {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case SchemaProofLinkRule( seq, link, ind::_ ) => {
      pProofLinkTerm( seq, omega, link, ind, cut_ancs)
    }
    case WeakeningRightRule(p, _, m) => {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case CutRule( p1, p2, _, a1, a2 ) => {
      val omega_ancs = getAncestors(omega)
      val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2 && !omega_ancs.contains(fo)),
                       p2.root.succedent.filter(fo => fo != a2 && !omega_ancs.contains(fo)))
      val w2 = Sequent(p1.root.antecedent.filter(fo => fo != a1 && !omega_ancs.contains(fo)),
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
        pTimes(pr.name, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs))
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
        pTimes(pr.name, extract(p1, omega, cut_ancs), extract(p2, omega, cut_ancs))
    }
    case NegLeftRule( p, _, a, m ) => {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case AndLeft1Rule(p, r, a, m) =>  {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case AndLeft2Rule(p, r, a, m) =>  {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case OrRight1Rule(p, r, a, m) =>  {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case OrRight2Rule(p, r, a, m) =>  {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case NegRightRule( p, _, a, m ) => {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case ContractionLeftRule(p, _, a1, a2, m) => {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case ContractionRightRule(p, _, a1, a2, m) => {
      if (getAncestors(omega).contains(m) || cut_ancs.contains(m))
        extract(p, omega, cut_ancs)
      else
        pUnary(pr.name, extract(p, omega, cut_ancs))
    }
    case AndEquivalenceRule1(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) || cut_ancs.contains(main))
        extract(up, omega, cut_ancs)
      else
        pUnary(pr.name, extract(up, omega, cut_ancs))
    }
    case AndEquivalenceRule2(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) || cut_ancs.contains(main))
        extract(up, omega, cut_ancs)
      else
        pUnary(pr.name, extract(up, omega, cut_ancs))
    }
    case AndEquivalenceRule3(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) || cut_ancs.contains(main))
        extract(up, omega, cut_ancs)
      else
        pUnary(pr.name, extract(up, omega, cut_ancs))
    }
    case OrEquivalenceRule1(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) || cut_ancs.contains(main))
        extract(up, omega, cut_ancs)
      else
        pUnary(pr.name, extract(up, omega, cut_ancs))
    }
    case OrEquivalenceRule2(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) || cut_ancs.contains(main))
        extract(up, omega, cut_ancs)
      else
        pUnary(pr.name, extract(up, omega, cut_ancs))
    }
    case OrEquivalenceRule3(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) || cut_ancs.contains(main))
        extract(up, omega, cut_ancs)
      else
        pUnary(pr.name, extract(up, omega, cut_ancs))
    }
    case _ => { println("ERROR in extraction of projection term : missing rule!");throw new Exception("ERROR in extract: ProjectionTermCreators") }
  }

  def omegaPrime(p: LKProof, seq: Sequent, omega: Set[FormulaOccurrence]): Set[FormulaOccurrence] = {
    val cut_anc_set = getCutAncestors(p)
    val omega_anc_set = omega.map(fo => getAncestors(fo)).foldLeft(Set.empty[FormulaOccurrence])((set,res) => set ++ res)
    (seq.antecedent++seq.succedent).filter(fo => (cut_anc_set++omega_anc_set).contains(fo)).toSet
  }
}



object PStructToExpressionTree {

  def apply(s: ProjectionTerm) : Tree[AnyRef] = s match {
     case pTimes(rho, left, right) => BinaryTree(new PTimesC(rho), apply(left), apply(right))
    case pPlus(seq1, seq2, left, right, w1, w2) => {
//      BinaryTreeWeak12(printSchemaProof.formulaToString(pPlusC), apply(left), apply(right), w1, w2)
      val t1 = if (w1.antecedent.isEmpty && w1.succedent.isEmpty) apply(left)
               else UnaryTree(new PWeakC(w1), apply(left))
      val t2 = if (w2.antecedent.isEmpty && w2.succedent.isEmpty) apply(right)
               else UnaryTree(new PWeakC(w2), apply(right))
      BinaryTree(PPlusC, t1, t2)

    }
    case pUnary(rho, upper) => UnaryTree(rho, apply(upper))
    case pAxiomTerm(seq) => {
      LeafTree(seq)
    }
    case pProofLinkTerm( seq, omega, proof_name, index, canc ) => {
      val cut_omega_anc = canc ++ getAncestors(omega)
      val seq1 = SchemaProofDB.get(proof_name).rec.root
      val len = StepMinusOne.lengthVar(index)
      val foccsInSeq = (seq.antecedent ++ seq.succedent).filter(fo => cut_omega_anc.contains(fo))
      var new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm]
      var sub = new SchemaSubstitution1[HOLExpression](new_map)
      if (len == 0) {
        new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], Succ(index) )
      }
      else
        if (len == 1)
          new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] //+ Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], index )
        else {
//          var new_term = index
//          for (i<-StepMinusOne.lengthVar(new_term) to 2 ) {
//            new_term = Pred(index)
//          }
          // TODO !!!
          new_map
        }
      sub = new SchemaSubstitution1[HOLExpression](new_map)
      val k = IntVar(new VariableStringSymbol("k")).asInstanceOf[Var]
      val trans_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(k, IntVar(new VariableStringSymbol("n")) )
      val trans_sub = new SchemaSubstitution1[HOLExpression](trans_map)
      val ms1 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms2 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms11 = foccsInSeq.filter(fo => seq.antecedent.contains(fo)).map(fo => trans_sub(sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])))).foldLeft(ms1)((res,f) => res + f.asInstanceOf[SchemaFormula])
      val ms22 = foccsInSeq.filter(fo => seq.succedent.contains(fo)).map(fo => trans_sub(sub(StepMinusOne.minusOne(fo.formula, k.asInstanceOf[IntVar])))).foldLeft(ms2)((res,f) => res + f.asInstanceOf[SchemaFormula])
//      ms11.foreach(f => println(printSchemaProof.formulaToString(f)))
//      print("\n\n\n")
//      ms22.foreach(f => println(printSchemaProof.formulaToString(f)))
//      print("\n\n\n")
      LeafTree(IndexedPredicate(new ProjectionSetSymbol(proof_name, (ms11,ms22)), index::Nil))
    }
  }


// for nice printing in console - the braces are with different colors and such things
  def applyConsole(s: ProjectionTerm) : Tree[String] = s match {

    case pTimes(rho, left, right) => BinaryTree[String](printSchemaProof.formulaToString(new PTimesC(""))+rho, applyConsole(left), applyConsole(right))
    case pPlus(seq1, seq2, left, right, w1, w2) => {
//      BinaryTreeWeak12(printSchemaProof.formulaToString(pPlusC), applyapply(left), applyapply(right), w1, w2)
      val t1 = UnaryTree[String]("w^{"+ printSchemaProof.sequentToString(w1) +"}", applyConsole(left))
      val t2 = UnaryTree[String]("w^{"+ printSchemaProof.sequentToString(w2) +"}", applyConsole(right))
      BinaryTree[String](printSchemaProof.formulaToString(PPlusC), t1, t2)

    }
    case pUnary(rho, upper) => UnaryTree[String](rho, applyConsole(upper))
//    case pProofLinkTerm(omega, proof_name, index) => LeafTree(new pProjSymbol(omega, index))
    case pAxiomTerm(seq) => {
//      println("pAxiomTerm "+ printSchemaProof.sequentToString(seq))
      LeafTree[String](printSchemaProof.sequentToString(seq))
    }
    case pProofLinkTerm( seq, omega, proof_name, index, ccanc ) => {
//      val cut_omega_anc = getCutAncestors(SchemaProofDB.get(proof_name).rec) ++ getAncestors(omega)
      val cut_omega_anc = ccanc ++ getAncestors(omega)
      val seq1 = SchemaProofDB.get(proof_name).rec.root
      val len = StepMinusOne.lengthVar(index)
      val foccsInSeq = (seq.antecedent ++ seq.succedent).filter(fo => cut_omega_anc.contains(fo))
      var new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm]
      var sub = new SchemaSubstitution1[HOLExpression](new_map)
      if (len == 0)
        new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] + Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], Succ(index) )
      else
        if (len == 1)
          new_map = scala.collection.immutable.Map.empty[Var, IntegerTerm] //+ Pair(IntVar(new VariableStringSymbol("k")).asInstanceOf[Var], index )
        else {
//          var new_term = index
//          for (i<-StepMinusOne.lengthVar(new_term) to 2 ) {
//            new_term = Pred(index)
//          }
          // TODO !!!
          new_map
        }
      sub = new SchemaSubstitution1[HOLExpression](new_map)
      var str = ""
      var str1 = ""
      if (foccsInSeq.size == 0)
        str = ""
      else if (foccsInSeq.size == 1)
        str = printSchemaProof.formulaToString(sub(foccsInSeq.head.formula))
      else
        str1 = foccsInSeq.tail.foldLeft(", ")((res,fo) => printSchemaProof.formulaToString(fo.formula)+res)
//        foccsInSeq.foldLeft(", ")((res,fo) => printSchemaProof.formulaToString(fo.formula)+res)
      LeafTree[String]("pr^"+Console.RESET+"{"+Console.CYAN+str+str1+Console.RESET+"},"+proof_name+"("+Console.MAGENTA+Console.UNDERLINED+printSchemaProof.formulaToString(index)+Console.RESET+")")
    }
  }


  // We define some symbols that represent the operations of the struct
 case class PTimesSymbol(val rho: String) extends LogicalSymbolsA {
    override def unique = "TimesSymbol"
    override def toString = "⊗_"+rho
    def toCode = "TimesSymbol"
  }

  case object PPlusSymbol extends LogicalSymbolsA {
    override def unique = "PlusSymbol"
    override def toString = "⊕"
    def toCode = "PlusSymbol"
  }

  case class PWeakSymbol(val seq: Sequent) extends LogicalSymbolsA {
    override def unique = "WeakSymbol"
    override def toString = "w^{"+seq.toString+"}"
    def toCode = "WeakSymbol"
  }

  class ProjectionSetSymbol (val name: String, val cut_occs: (Multiset[SchemaFormula], Multiset[SchemaFormula])) extends ConstantSymbolA {
    def compare( that: SymbolA ) : Int =
      // TODO: implement
      throw new Exception

    def toCode() : String =
      // TODO: implement
      throw new Exception

    override def toString() =
      "pr^{(" + cutConfToString(cut_occs) + ")," + name +"}"

    private def cutConfToString( cc : (Multiset[SchemaFormula], Multiset[SchemaFormula]) ) = {
      def str( m : Multiset[SchemaFormula] ) = m.foldLeft( "" )( (s, f) => s + f.toStringSimple )
      str( cc._1 ) + "|" + str( cc._2 )
    }
  }

  case class PTimesC(val rho: String) extends HOLConst(new PTimesSymbol(rho), "( o -> (o -> o) )")
  case object PPlusC extends HOLConst(PPlusSymbol, "( o -> (o -> o) )")
  case class PWeakC(val seq: Sequent) extends HOLConst(new PWeakSymbol(seq), "(o -> o)")


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
      printTree(up)
    }

//    case BinaryTreeWeak12(vert, up1, up2, w1, w2) => {
//      print(Console.BLUE+" ("+Console.RESET+" w^{"+Console.YELLOW+printSchemaProof.sequentToString(w1)+Console.RESET+"}")
//      printTree(up1)
//      print(" "+Console.BLUE)
//      print("\n\n                                  "+vert+"\n\n")
//      print(Console.RESET+" w^{"+Console.YELLOW+printSchemaProof.sequentToString(w2)+Console.RESET+"}")
//      printTree(up2)
//      print(Console.BLUE+")"+Console.RESET)
//    }

    case BinaryTree(vert, up1, up2) => {
      if (vert == PPlusSymbol.toString)
        print(Console.BLUE)
      else
        print(Console.RED)
      print("(")
      print(Console.RESET)
      printTree(up1)
      if (vert == PPlusSymbol.toString) {
        print(Console.BLUE)
        print("\n\n                                   "+vert+"\n\n")
      }
      else {
        print(Console.RED)
        print(" "+vert+" ")
      }

      print(Console.RESET)
      printTree(up2)
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

//class BinaryTreeWeak12(override val vertex: String, override val t1: Tree[String], override val t2: Tree[String], val w1: Sequent, val w2: Sequent) extends BinaryTree[String](vertex, t1, t2)
//
//object BinaryTreeWeak12 {
//  def apply(vertex: String, t1: Tree[String], t2: Tree[String], w1:Sequent, w2:Sequent) = {
//    new BinaryTreeWeak12(vertex, t1, t2, w1, w2)
//  }
//  def unapply(t: Tree[String]) = t match {
//    case t: BinaryTreeWeak12 => Some((t.vertex, t.t1, t.t2, t.w1, t.w2))
//    case t: Tree[_] => None
//  }
//}

