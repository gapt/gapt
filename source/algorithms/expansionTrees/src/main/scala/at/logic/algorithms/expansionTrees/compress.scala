
package at.logic.algorithms.expansionTrees

import at.logic.calculi.expansionTrees._
import at.logic.calculi.expansionTrees.multi.{WeakQuantifier => mWeakQuantifier, StrongQuantifier => mStrongQuantifier, And => mAnd, Or => mOr, Imp => mImp, Not => mNot, Atom => mAtom, SkolemQuantifier => mSkolemQuantifier, MultiExpansionTree, MultiExpansionSequent}
import at.logic.language.hol.{HOLConst, HOLExpression, HOLVar, ExVar, AllVar, HOLFormula, Substitution, instantiate}
import at.logic.utils.dssupport.ListSupport.{groupSeq}

/** Converts an ExpansionTree to a MultiExpansionTree by squishing quantifiers together into blocks.
  * There is also an apply method for sequents.
  */  
object compressQuantifiers {
  def apply(tree: ExpansionTree): MultiExpansionTree = tree match {
    case Atom(f) => mAtom(f)
    case Neg(t1) => mNot(compressQuantifiers(t1))
    case And(t1,t2) => mAnd(compressQuantifiers(t1), compressQuantifiers(t2))
    case Or(t1,t2) => mOr(compressQuantifiers(t1), compressQuantifiers(t2))
    case Imp(t1,t2) => mImp(compressQuantifiers(t1), compressQuantifiers(t2))
    case WeakQuantifier(f,is) => mWeakQuantifier(f, is.flatMap(x => compressWeak(compressQuantifiers(x._1),x._2)))
    case StrongQuantifier(f,v,t) => val (sel, vars) =
      compressStrong(compressQuantifiers(t),v);
      mStrongQuantifier(f, vars,sel)
    case SkolemQuantifier(f,cs,t) =>
      val (sel, skcs) = compressSkolem(compressQuantifiers(t),cs);
      mSkolemQuantifier(f, skcs,sel)
  }
  
  def apply(sequent: ExpansionSequent): MultiExpansionSequent = MultiExpansionSequent(sequent.antecedent.map(this.apply), sequent.succedent.map(this.apply))

  private def compressStrong(tree: MultiExpansionTree, v: HOLVar): Tuple2[MultiExpansionTree, Seq[HOLVar]] = tree match {
    case mStrongQuantifier(_, vars, sel) => (sel, vars.+:(v))
    case _ => (tree, List(v))
  }

  private def compressSkolem(tree: MultiExpansionTree, sk: HOLExpression): Tuple2[MultiExpansionTree, Seq[HOLExpression]] = tree match {
    case mSkolemQuantifier(_, cs, sel) => (sel, cs.+:(sk))
    case _ => (tree, List(sk))
  }

  private def compressWeak(tree: MultiExpansionTree, e: HOLExpression): Seq[Tuple2[MultiExpansionTree, Seq[HOLExpression]]] = tree match {
    case mWeakQuantifier(_, is) => is.map(x => (x._1, x._2.+:(e)))
    case _ => List((tree, List(e)))
  }
}

/** Converts a MultiExpansionTree to an ExpansionTree by picking quantifier blocks apart.
  * There is also an apply method for sequents. The interesting parts happen in the private methods decompress{Strong,Weak,Skolem}.
  */ 
object decompressQuantifiers {
  def apply(tree: MultiExpansionTree): ExpansionTree = tree match {
    case mAtom(f) => Atom(f)
    case mNot(t1) => Neg(decompressQuantifiers(t1))
    case mAnd(t1,t2) => And(decompressQuantifiers(t1), decompressQuantifiers(t2))
    case mOr(t1,t2) => Or(decompressQuantifiers(t1), decompressQuantifiers(t2))
    case mImp(t1,t2) => Imp(decompressQuantifiers(t1), decompressQuantifiers(t2))
    
    case mStrongQuantifier(f, eig, sel) => {
      val selNew = decompressQuantifiers(sel)
      decompressStrong(f, eig, selNew)
    }
    
    case mSkolemQuantifier(f, exp, sel) => {
      val selNew = decompressQuantifiers(sel)
      decompressSkolem(f, exp, selNew)
    }
    
    case mWeakQuantifier(f, instances) => {
      val instancesNew = instances.map(p => (decompressQuantifiers(p._1), p._2))
      decompressWeak(f, instancesNew)
      
    }
  }
  
  def apply(sequent: MultiExpansionSequent): ExpansionSequent = ExpansionSequent(sequent.antecedent.map(this.apply), sequent.succedent.map(this.apply))
  
  private def decompressStrong(f: HOLFormula, eig: Seq[HOLVar], sel: ExpansionTree): ExpansionTree = f match {
    case AllVar(v, subF) => StrongQuantifier(f, eig.head, decompressStrong(instantiate(f,eig.head), eig.tail, sel))
    case ExVar(v, subF) => StrongQuantifier(f, eig.head, decompressStrong(instantiate(f,eig.head), eig.tail, sel))
    case _ => sel   
  }
  
  private def decompressSkolem(f: HOLFormula, exp: Seq[HOLExpression], sel: ExpansionTree): ExpansionTree = f match {
    case AllVar(v, subF) => SkolemQuantifier(f, exp.head, decompressSkolem(instantiate(f,exp.head), exp.tail, sel))
    case ExVar(v, subF) => SkolemQuantifier(f, exp.head, decompressSkolem(instantiate(f,exp.head), exp.tail, sel))
    case _ => sel   
  }
  
  private def decompressWeak(f: HOLFormula, instances: Seq[(ExpansionTree, Seq[HOLExpression])]): ExpansionTree = f match {
    case ExVar(v, subF) => {
      val foo = groupSeq(instances.map(p => (p._2.head, p._1, p._2.tail)), (t: Tuple3[HOLExpression, ExpansionTree, Seq[HOLExpression]]) => t._1).map(l => (l.head._1, l.map(t => (t._2, t._3)))) // Result: foo is a list of elements of the form (t, [(E_1, s_1),..,(E_n, s_n)]). I am so sorry for this.
      val fooNew = foo.map(p => (p._1, decompressWeak(instantiate(f,p._1), p._2))) // Result: fooNew is a list of elements of the form (t, E)
      merge(WeakQuantifier(f, fooNew.map(p => (p._2, p._1)))) // Why is it necessary to use merge here?
    }
    
    case AllVar(v, subF) => { // This case is exactly the same as the previous one.
      val foo = groupSeq(instances.map(p => (p._2.head, p._1, p._2.tail)), (t: Tuple3[HOLExpression, ExpansionTree, Seq[HOLExpression]]) => t._1).map(l => (l.head._1, l.map(t => (t._2, t._3))))
      val fooNew = foo.map(p => (p._1, decompressWeak(instantiate(f,p._1), p._2)))
      merge(WeakQuantifier(f, fooNew.map(p => (p._2, p._1))))
    }
    
    case _ => instances.head._1
  }
}