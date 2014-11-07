
package at.logic.algorithms.expansionTrees

import at.logic.calculi.expansionTrees._
import at.logic.calculi.expansionTrees.{MWeakQuantifier, MStrongQuantifier, MAnd, MOr, MImp, MNeg, MAtom, MSkolemQuantifier, MultiExpansionTree, MultiExpansionSequent}
import at.logic.language.hol.{HOLExpression, HOLVar, ExVar, AllVar, HOLFormula, instantiate}
import at.logic.utils.dssupport.ListSupport.groupSeq

/**
  * Converts an ExpansionTree to a MultiExpansionTree by squishing quantifiers together into blocks.
  * Can also be called on ExpansionSequents.
  */  
object compressQuantifiers {

  /**
   * Compresses an ExpansionTree.
   * @param tree The ExpansionTree to be compressed.
   * @return The corresponding MultiExpansionTree.
   */
  def apply(tree: ExpansionTree): MultiExpansionTree = tree match {
    case Atom(f) => MAtom(f)
    case Neg(t1) => MNeg(compressQuantifiers(t1))
    case And(t1,t2) => MAnd(compressQuantifiers(t1), compressQuantifiers(t2))
    case Or(t1,t2) => MOr(compressQuantifiers(t1), compressQuantifiers(t2))
    case Imp(t1,t2) => MImp(compressQuantifiers(t1), compressQuantifiers(t2))
    case WeakQuantifier(f,is) => MWeakQuantifier(f, is.flatMap(x => compressWeak(compressQuantifiers(x._1),x._2)))
    case StrongQuantifier(f,v,t) => val (sel, vars) =
      compressStrong(compressQuantifiers(t),v)
      MStrongQuantifier(f, vars,sel)
    case SkolemQuantifier(f,cs,t) =>
      val (sel, skcs) = compressSkolem(compressQuantifiers(t),cs)
      MSkolemQuantifier(f, skcs,sel)
  }

  /**
   * Compresses an ExpansionSequent by mapping over the antecedent and succedent.
   * @param sequent The ExpansionSequent to be compressed.
   * @return The corresponding MultiExpansionSequent.
   */
  def apply(sequent: ExpansionSequent): MultiExpansionSequent = MultiExpansionSequent(sequent.antecedent.map(this.apply), sequent.succedent.map(this.apply))

  private def compressStrong(tree: MultiExpansionTree, v: HOLVar): Tuple2[MultiExpansionTree, Seq[HOLVar]] = tree match {
    case MStrongQuantifier(_, vars, sel) => (sel, vars.+:(v))
    case _ => (tree, List(v))
  }

  private def compressSkolem(tree: MultiExpansionTree, sk: HOLExpression): Tuple2[MultiExpansionTree, Seq[HOLExpression]] = tree match {
    case MSkolemQuantifier(_, cs, sel) => (sel, cs.+:(sk))
    case _ => (tree, List(sk))
  }

  private def compressWeak(tree: MultiExpansionTree, e: HOLExpression): Seq[Tuple2[MultiExpansionTree, Seq[HOLExpression]]] = tree match {
    case MWeakQuantifier(_, is) => is.map(x => (x._1, x._2.+:(e)))
    case _ => List((tree, List(e)))
  }
}

/**
  * Converts a MultiExpansionTree to an ExpansionTree by picking quantifier blocks apart.
  * Can also be called on MultiExpansionSequents.
  * The interesting parts happen in the private methods decompress{Strong,Weak,Skolem}.
  */ 
object decompressQuantifiers {

  /**
   * Decompresses a MultiExpansionTree.
   * @param tree The MultiExpansionTree to be decompressed.
   * @return The corresponding ExpansionTree.
   */
  def apply(tree: MultiExpansionTree): ExpansionTree = tree match {
    case MAtom(f) => Atom(f)
    case MNeg(t1) => Neg(decompressQuantifiers(t1))
    case MAnd(t1,t2) => And(decompressQuantifiers(t1), decompressQuantifiers(t2))
    case MOr(t1,t2) => Or(decompressQuantifiers(t1), decompressQuantifiers(t2))
    case MImp(t1,t2) => Imp(decompressQuantifiers(t1), decompressQuantifiers(t2))
    
    case MStrongQuantifier(f, eig, sel) =>
      val selNew = decompressQuantifiers(sel)
      decompressStrong(f, eig, selNew)

    case MSkolemQuantifier(f, exp, sel) =>
      val selNew = decompressQuantifiers(sel)
      decompressSkolem(f, exp, selNew)

    case MWeakQuantifier(f, instances) =>
      val instancesNew = instances.map(p => (decompressQuantifiers(p._1), p._2))
      decompressWeak(f, instancesNew)
  }

  /**
   * Decompresses a MultiExpansionSequent by mapping over the antecedent and succedent.
   * @param sequent The MultiExpansionSequent to be decompressed.
   * @return The corresponding ExpansionSequent.
   */
  def apply(sequent: MultiExpansionSequent): ExpansionSequent = ExpansionSequent(sequent.antecedent.map(this.apply), sequent.succedent.map(this.apply))
  
  private def decompressStrong(f: HOLFormula, eig: Seq[HOLVar], sel: ExpansionTree): ExpansionTree = f match {
    case AllVar(_,_) | ExVar(_,_) => StrongQuantifier(f, eig.head, decompressStrong(instantiate(f,eig.head), eig.tail, sel))
    case _ => sel   
  }
  
  private def decompressSkolem(f: HOLFormula, exp: Seq[HOLExpression], sel: ExpansionTree): ExpansionTree = f match {
    case AllVar(_,_) | ExVar(_,_) => SkolemQuantifier(f, exp.head, decompressSkolem(instantiate(f,exp.head), exp.tail, sel))
    case _ => sel   
  }
  
  private def decompressWeak(f: HOLFormula, instances: Seq[(ExpansionTree, Seq[HOLExpression])]): ExpansionTree = f match {
    case ExVar(_,_) | AllVar(_,_) =>
      val groupedInstances = groupSeq(instances.map(p => (p._2.head, p._1, p._2.tail)), (t: (HOLExpression, ExpansionTree, Seq[HOLExpression])) => t._1).map(l => (l.head._1, l.map(t => (t._2, t._3)))) // Result: groupedInstances is a list of elements of the form (t, [(E_1, s_1),..,(E_n, s_n)]).
      val newInstances = groupedInstances.map(p => (p._1, decompressWeak(instantiate(f,p._1), p._2))) // Result: newInstances is a list of elements of the form (t, E)
      merge(WeakQuantifier(f, newInstances.map(p => (p._2, p._1))))

    case _ => instances.head._1
  }
}