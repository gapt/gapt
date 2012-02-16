package at.logic.transformations.ceres

import _root_.at.logic.calculi.lk.lkExtractors.{BinaryLKProof, UnaryLKProof}
import at.logic.calculi.slk.AndEquivalenceRule1._
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

//import scala.collection.mutable.{Map, HashMap}
import unfolding.{StepMinusOne, SchemaSubstitution1}


//import struct._
import at.logic.language.lambda.types.ImplicitConverters._

trait ProjectionTerm

class pTimes(val rho: String, val left: ProjectionTerm, val right: ProjectionTerm) extends ProjectionTerm
class pPlus(val seq1: Sequent, val seq2: Sequent, val left: ProjectionTerm, val right: ProjectionTerm, val w1: Sequent, val w2: Sequent) extends ProjectionTerm
class pUnary(val rho: String, val upper: ProjectionTerm) extends ProjectionTerm
class pProofLinkTerm(val seq: Sequent, val omega: Set[FormulaOccurrence], val proof_name: String, val index: IntegerTerm, val p_old: LKProof) extends ProjectionTerm
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
  def apply(seq: Sequent, omega: Set[FormulaOccurrence], proof_name: String, index: IntegerTerm, p_old: LKProof) = {
    new pProofLinkTerm(seq, omega, proof_name, index, p_old)
  }
  def unapply(term : ProjectionTerm) = term match {
    case t: pProofLinkTerm => Some((t.seq, t.omega, t.proof_name, t.index, t.p_old))
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

class ProjectionTermCreators(val ccmap: scala.collection.immutable.Map[String, List[FormulaOccurrence]]) {}

object ProjectionTermCreators {
  def apply(ccmap: scala.collection.immutable.Map[String, List[FormulaOccurrence]]) = {
    new ProjectionTermCreators(ccmap)
  }

  def genCC(proof_name: String): List[(String,Tree[String])] = {
//    val p_base = SchemaProofDB.get(proof_name).base
    val p_rec = SchemaProofDB.get(proof_name).rec
////    extract(SchemaProofDB.get(proof_name).base, )
//    val cc = getCC(p_rec, List.empty[FormulaOccurrence], p_rec) ++ (new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int]), new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int]))
    val cclist = if (getCC(p_rec, List.empty[FormulaOccurrence], p_rec).contains((proof_name, List.empty[FormulaOccurrence])))
      getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    else
      (proof_name, List.empty[FormulaOccurrence]) :: getCC(p_rec, List.empty[FormulaOccurrence], p_rec)
    cclist.foreach(pair => {
      println("\n\n\n"+pair._1 +" : ")
      pair._2.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    })
    cclist.map(pair => (pair._1, PStructToExpressionTree.applyConsole(extract(SchemaProofDB.get(pair._1).rec, pair._2.toSet, SchemaProofDB.get(pair._1).rec))))
  }



  def getCC(p: LKProof, omega: List[FormulaOccurrence], p_old: LKProof): List[(String, List[FormulaOccurrence])] = p match {
    case SchemaProofLinkRule( seq, proof_name, index::_ ) => {
      val cut_omega_anc = getCutAncestors(p_old) ++ getAncestors(omega.toSet)
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
      val fcc = foccsInSeq.map(fo => sub(fo.formula))
      (proof_name, (seq1.antecedent ++ seq1.succedent).toList.filter(fo => fcc.contains(fo.formula)))::Nil
    }
    case Axiom(so) => List.empty[(String, List[FormulaOccurrence])]
    case UnaryTree(_,up) => getCC(up.asInstanceOf[LKProof], omega, p_old)
    case BinaryTree(_, up1, up2) => getCC(up1.asInstanceOf[LKProof], omega, p_old) ++ getCC(up2.asInstanceOf[LKProof], omega, p_old)
  }



  def extract(pr: LKProof, omega: Set[FormulaOccurrence], p_old: LKProof): ProjectionTerm = pr match {
    case Axiom(ro) => pAxiomTerm(ro)
    case WeakeningLeftRule(p, _, m) => {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(m))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case SchemaProofLinkRule( seq, link, ind::_ ) => {
      pProofLinkTerm( seq, omega, link, ind, p_old)
    }
    case WeakeningRightRule(p, _, m) => {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(m))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case CutRule( p1, p2, _, a1, a2 ) => {
      val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2 && !getAncestors(omega).contains(fo)), p2.root.succedent.filter(fo => fo != a2 && !getAncestors(omega).contains(fo)))
      val w2 = Sequent(p1.root.antecedent.filter(fo => fo != a1 && !getAncestors(omega).contains(fo)), p1.root.succedent.filter(fo => fo != a1 && !getAncestors(omega).contains(fo)))
      pPlus(p1.root, p2.root, extract(p1, omega, p_old), extract(p2, omega, p_old), w1, w2)
    }
    case OrLeftRule(p1, p2, _, a1, a2, m) => {
      if (getAncestors(omega).contains(a1) && getAncestors(omega).contains(a2)) {
        val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2), p2.root.succedent.filter(fo => fo != a2))
        val w2 = Sequent(p1.root.antecedent.filter(fo => fo != a1), p1.root.succedent.filter(fo => fo != a1))
        pPlus(p1.root, p2.root, extract(p1, omega, p_old), extract(p2, omega, p_old), w1, w2)
      }
      else
        pTimes(pr.name, extract(p1, omega, p_old), extract(p2, omega, p_old))
    }
    case AndRightRule(p1, p2, _, a1, a2, m) => {
      if (getAncestors(omega).contains(a1) && getAncestors(omega).contains(a2) &&
          !getCutAncestors(p_old).contains(a1) && !getCutAncestors(p_old).contains(a2)) {
        val w1 = Sequent(p2.root.antecedent.filter(fo => fo != a2), p2.root.succedent.filter(fo => fo != a2))
        val w2 = Sequent(p1.root.antecedent.filter(fo => fo != a1), p1.root.succedent.filter(fo => fo != a1))
        pPlus(p1.root, p2.root, extract(p1, omega, p_old), extract(p2, omega, p_old), w1, w2)
      }
      else
        pTimes(pr.name, extract(p1, omega, p_old), extract(p2, omega, p_old))
    }
    case NegLeftRule( p, _, a, m ) => {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(a))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case AndLeft1Rule(p, r, a, m) =>  {
        if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(a))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case AndLeft2Rule(p, r, a, m) =>  {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(a))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case OrRight1Rule(p, r, a, m) =>  {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(a))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case OrRight2Rule(p, r, a, m) =>  {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(a))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case NegRightRule( p, _, a, m ) => {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(a))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case ContractionLeftRule(p, _, a1, a2, m) => {
      if (getAncestors(omega).contains(m) && !getCutAncestors(p_old).contains(m))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case ContractionRightRule(p, _, a1, a2, m) => {
      if (getAncestors(omega).contains(m)  && !getCutAncestors(p_old).contains(m))
        extract(p, omega, p_old)
      else
        pUnary(pr.name, extract(p, omega, p_old))
    }
    case AndEquivalenceRule1(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) && !getCutAncestors(p_old).contains(main))
        extract(up, omega, p_old)
      else
        pUnary(pr.name, extract(up, omega, p_old))
    }
    case AndEquivalenceRule2(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) && !getCutAncestors(p_old).contains(main))
        extract(up, omega, p_old)
      else
        pUnary(pr.name, extract(up, omega, p_old))
    }
    case AndEquivalenceRule3(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) && !getCutAncestors(p_old).contains(main))
        extract(up, omega, p_old)
      else
        pUnary(pr.name, extract(up, omega, p_old))
    }
    case OrEquivalenceRule1(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main))
        extract(up, omega, p_old)
      else
        pUnary(pr.name, extract(up, omega, p_old))
    }
    case OrEquivalenceRule2(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) && !getCutAncestors(p_old).contains(main))
        extract(up, omega, p_old)
      else
        pUnary(pr.name, extract(up, omega, p_old))
    }
    case OrEquivalenceRule3(up, r, aux, main) =>  {
      if (getAncestors(omega).contains(main) && !getCutAncestors(p_old).contains(main))
        extract(up, omega, p_old)
      else
        pUnary(pr.name, extract(up, omega, p_old))
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
      val t1 = UnaryTree(new PWeakC(w1), apply(left))
      val t2 = UnaryTree(new PWeakC(w2), apply(right))
      BinaryTree(PPlusC, t1, t2)

    }
    case pUnary(rho, upper) => UnaryTree(rho, apply(upper))
    case pAxiomTerm(seq) => {
      LeafTree(seq)
    }
    case pProofLinkTerm( seq, omega, proof_name, index, p_old ) => {
      val cut_omega_anc = getCutAncestors(p_old) ++ getAncestors(omega)
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
      val ms1 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms11 = foccsInSeq.filter(fo => seq.antecedent.contains(fo)).map(fo => sub(fo.formula)).foldLeft(ms1)((res,f) => res + f.asInstanceOf[SchemaFormula])
      val ms2 = new Multisets.HashMultiset[SchemaFormula](HashMap.empty[SchemaFormula, Int])
      val ms22 = foccsInSeq.filter(fo => seq.succedent.contains(fo)).map(fo => sub(fo.formula)).foldLeft(ms2)((res,f) => res + f.asInstanceOf[SchemaFormula])

      LeafTree(IndexedPredicate(new ProjectionSetSymbol(proof_name, (ms11,ms22)), index::Nil))
    }
  }


// for nice printing in console - the braces are with different colors and such things
  def applyConsole(s: ProjectionTerm) : Tree[String] = s match {

    case pTimes(rho, left, right) => BinaryTree[String](printSchemaProof.formulaToString(new PTimesC(""))+"_"+rho, applyConsole(left), applyConsole(right))
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
    case pProofLinkTerm( seq, omega, proof_name, index, p_old ) => {
//      val cut_omega_anc = getCutAncestors(SchemaProofDB.get(proof_name).rec) ++ getAncestors(omega)
      val cut_omega_anc = getCutAncestors(p_old) ++ getAncestors(omega)
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

