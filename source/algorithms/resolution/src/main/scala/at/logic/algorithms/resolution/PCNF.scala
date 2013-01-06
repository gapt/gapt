package at.logic.algorithms.resolution

import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.resolution.base.FClause
import at.logic.language.hol._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.quantificationRules.{ExistsRightRule, ForallLeftRule}
import at.logic.calculi.lk.base.types.FSequent
import scala.Some
import scala.Tuple2

/**
 * Given a formula f and a clause a in CNF(-f), PCNF computes a proof of s o a (see logic.at/ceres for the definition of o)
 */
object PCNF {
  /**
   * @param s a sequent not containing strong quantifiers
   * @param a a clause
   * @return an LK proof of s o a (see logic.at/ceres for the definition of o)
   */
  def apply(s: FSequent, a: FClause): LKProof = {
    // compute formula
    val form = if (!s.antecedent.isEmpty)
      s.succedent.foldLeft(s.antecedent.reduceLeft((f1,f2) => And(f1,f2)))((f1,f2) => And(f1,Neg(f2)))
    else
      s.succedent.tail.foldLeft(Neg(s.succedent.head))((f1,f2) => And(f1,Neg(f2)))

    // compute CNF and confirm a <- CNF(-s)
    val cnf = CNFp(form)
    if (!cnf.contains(a)) throw new IllegalArgumentException("Clause a [" + a.toString + "] is not contained in CNF(-s) [\n" + cnf.mkString(";\n") + "\n]")

    // find the right formula and compute the proof
    val (p,f,inAntecedent) = s.antecedent.find(x => CNFp(x).contains(a)) match {
      case Some(f) => (PCNFp(f,a),f,true)
      case _ => {
        val f = s.succedent.find(x => CNFn(x).contains(a)).get
        (PCNFn(f,a),f,false)
      }
    }

    // apply weakenings
    (if (!inAntecedent) removeFirst(s.succedent,f) else s.succedent).foldLeft(
      (if (inAntecedent) (removeFirst(s.antecedent,f)) else s.antecedent).foldLeft(p)((pr,f) => WeakeningLeftRule(pr,f))
    )((pr,f) => WeakeningRightRule(pr,f))
  }

  /**
   * assuming a in CNF^-(f) we give a proof of a o |- f
   * @param f
   * @param a
   * @return
   */
  private def PCNFn(f: HOLFormula, a: FClause): LKProof = f match {
    case Atom(_,_) => Axiom(List(f),List(f))
    case Neg(f2) => NegRightRule(PCNFp(f2,a), f2)
    case And(f1,f2) => {
      /* see Or in PCNFp
      // get all possible partitions of the ant and suc of the clause a
      val prod = for ((c1,c2) <- power(a.neg.toList); (d1,d2) <- power(a.pos.toList)) yield (FClause(c1,d1),FClause(c2,d2))
      // find the right partition
      val cnf1 = CNFn(f1)
      val cnf2 = CNFn(f2)
      val par = prod.find(x => cnf1.contains(x._1) && cnf2.contains(x._2)).get
      // create the proof
      AndRightRule(PCNFn(f1,par._1), PCNFn(f2,par._2), f1, f2)
      */
      AndRightRule(PCNFn(f1,a), PCNFn(f2,a), f1, f2)
    }
    case Or(f1,f2) =>
      if (CNFn(f1).contains(a)) OrRight1Rule(PCNFn(f1,a),f1,f2)
      else OrRight2Rule(PCNFn(f2,a),f1,f2)
    case Imp(f1,f2) =>
      if (CNFp(f1).contains(a)) ImpRightRule(WeakeningRightRule(PCNFp(f1,a), f2), f1,f2)
      else ImpRightRule(WeakeningLeftRule(PCNFn(f2,a), f1), f1, f2)
    case ExVar(v,f2) => ExistsRightRule(PCNFn(f2, a), f2 ,f, v.asInstanceOf[HOLVar])
    case _ => throw new IllegalArgumentException("unknown head of formula: " + a.toString)
  }

  /**
   * assuming a in CNF^+(f) we give a proof of a o f |-
   * @param f
   * @param a
   * @return
   */
  private def PCNFp(f: HOLFormula, a: FClause): LKProof = f match {
    case Atom(_,_) => Axiom(List(f),List(f))
    case Neg(f2) => NegLeftRule(PCNFn(f2,a), f2)
    case And(f1,f2) =>
      if (CNFp(f1).contains(a)) AndLeft1Rule(PCNFp(f1,a),f1,f2)
      else AndLeft2Rule(PCNFp(f2,a),f1,f2)
    case Or(f1,f2) => {
      /* the following is an inefficient way to compute the exact context sequents
      // get all possible partitions of the ant and suc of the clause a
      val prod = for ((c1,c2) <- power(a.neg.toList); (d1,d2) <- power(a.pos.toList)) yield (FClause(c1,d1),FClause(c2,d2))
      // find the right partition
      val cnf1 = CNFp(f1)
      val cnf2 = CNFp(f2)
      val par = prod.find(x => cnf1.contains(x._1) && cnf2.contains(x._2)).get
      // create the proof
      OrLeftRule(PCNFp(f1,par._1), PCNFp(f2,par._2), f1, f2)
      we just take the whole context and apply weakenings later */
      OrLeftRule(PCNFp(f1,a), PCNFp(f2,a), f1, f2)
    }
    case Imp(f1,f2) => {
      // get all possible partitions of the ant and suc of the clause a
      val prod = for ((c1,c2) <- power(a.neg.toList); (d1,d2) <- power(a.pos.toList)) yield (FClause(c1,d1),FClause(c2,d2))
      // find the right partition
      val cnf1 = CNFn(f1)
      val cnf2 = CNFp(f2)
      val par = prod.find(x => cnf1.contains(x._1) && cnf2.contains(x._2)).get
      // create the proof
      ImpLeftRule(PCNFn(f1,par._1), PCNFp(f2,par._2), f1, f2)
    }
    case AllVar(v,f2) => ForallLeftRule(PCNFp(f2, a), f2, f, v.asInstanceOf[HOLVar])
    case _ => throw new IllegalArgumentException("unknown head of formula: " + a.toString)
  }

  // we need to compute the power set of the literals of the clause in order to find the right division of them in and right and or left
  def power[A](lst: List[A]): List[Tuple2[List[A],List[A]]] = {
    @annotation.tailrec
    def pwr(s: List[A], acc: List[Tuple2[List[A],List[A]]]): List[Tuple2[List[A],List[A]]] = s match {
      case Nil     => acc
      case a :: as => pwr(as, acc ::: (acc map (x => (a :: x._1,removeFirst(x._2,a).toList))))
    }
    pwr(lst, (Nil,lst) :: Nil)
  }

  def removeFirst[A](s: Seq[A], a: A): Seq[A] = {
    val index = s.indexOf(a)
    s.take(index) ++ s.takeRight(s.size-index-1)
  }
}

