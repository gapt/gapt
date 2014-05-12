package at.logic.algorithms.resolution

import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.resolution.base.FClause
import at.logic.language.hol._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.quantificationRules.{ExistsRightRule, ForallLeftRule}
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.lambda.substitutions.Substitution
import scala.Some
import scala.Tuple2
import at.logic.algorithms.lk.{applySubstitution => applySub, addContractions, addWeakenings}
import at.logic.calculi.resolution.robinson.RobinsonResolutionProof

/**
 * Given a formula f and a clause a in CNF(-f), PCNF computes a proof of s o a (see logic.at/ceres for the definition of o)
 * Note about checking containmenet up to variables renaming:
 * we compute the variable renaming from the lk proof to the resolution proof for a specific clause. We cannot apply it to the formula in s
  as it might be quantified over this variables so we apply it to the resulted lk proof. We must apply it as otherwise the substitution in
 * the resolution to lk transformation will not be applied to these clauses. In the weakenings application at the end of this method we try
 * to apply it to the formulas as well as if it is quantified over these variables, it will be also quantified in the proof so no damage
 * done.
 */
case class ResolutionException(msg : String, proofs : List[RobinsonResolutionProof], clauses: List[FClause])
  extends Exception("Resolution Exception: "+msg)

object PCNF {
  /**
   * @param s a sequent not containing strong quantifiers
   * @param a a clause in the CNF of -s
   * @return an LK proof of s o a (see logic.at/ceres for the definition of o)
   */
  def apply(s: FSequent, a: FClause): LKProof = {
    // compute formula
    val form = if (!s.antecedent.isEmpty)
      s.succedent.foldLeft(s.antecedent.reduceLeft((f1,f2) => And(f1,f2)))((f1,f2) => And(f1,Neg(f2)))
    else
      s.succedent.tail.foldLeft(Neg(s.succedent.head))((f1,f2) => And(f1,Neg(f2)))

    // compute CNF and confirm a <- CNF(-s) up to variable renaming
    val cnf = CNFp(form)
    var sub = Substitution[HOLExpression]()
    var subi = Substitution[HOLExpression]()
    val op = cnf.find(y => getVariableRenaming(y,a) match {
      case Some(s) => {sub = s; subi = getVariableRenaming(a,y).get; true}
      case _ => false
    })
    val (p,f,inAntecedent) = op match {
      case Some(f2) => {
        // find the right formula and compute the proof
        s.antecedent.find(x => containsMatchingClause(f2,CNFp(x))) match {
          case Some(f3) => {
            (applySub(PCNFp(f3,a,subi),sub)._1,f3,true)
          }
          case _ => {
            val f3 = s.succedent.find(x => containsMatchingClause(f2,CNFn(x))).get
            (applySub(PCNFn(f3,a,subi),sub)._1,f3,false)
          }
        }
      }
      case None =>
        // check for tautology
        a.pos.find(p => a.neg.exists( n => n == p )) match {
          case Some(f) => (Axiom(a.neg, a.pos), f.asInstanceOf[HOLFormula], false)
          case _ => 
        // check for reflexivity
          a.pos.find(f => f match {
            case Equation(a,b) if a == b => true
            case at.logic.language.fol.Equation(a,b) if a == b => true // TOFIX: remove when bug 224 is solved
            case  _ => false
          }) match {
           case Some(f) => (Axiom(List(),List(f)),f.asInstanceOf[HOLFormula],false)
            case _ => throw new ResolutionException("Clause [" + a.toString + "] is not reflexivity and not contained in CNF(-s) [\n" + cnf.mkString(";\n") + "\n]", Nil, a::cnf.toList )
          }
        }
    }
    // apply weakenings
    /*(if (!inAntecedent) removeFirst(s.succedent,f) else s.succedent).foldLeft(
      (if (inAntecedent) (removeFirst(s.antecedent,f)) else s.antecedent).foldLeft(p)((pr,f)
        => WeakeningLeftRule(pr,sub(f).asInstanceOf[HOLFormula]))
    )((pr,f) => WeakeningRightRule(pr,sub(f).asInstanceOf[HOLFormula]))*/

    //val missing_literals = s diff p.root.toFSequent
    val p1 = if (inAntecedent) {
      addWeakenings.weaken(p, FSequent(sub(f).asInstanceOf[HOLFormula]::Nil, Nil) compose a.toFSequent)
    } else {
      addWeakenings.weaken(p, FSequent(Nil,sub(f).asInstanceOf[HOLFormula]::Nil) compose a.toFSequent)
    }
    val p2 = addContractions.contract(p1, s compose a.toFSequent)
    p2

    // apply contractions on the formulas of a, since we duplicate the context on every binary rule
    //introduceContractions(p_,a)
  }

  def containsMatchingClause(what : FClause, where : Set[FClause]) : Boolean = {
    //TODO: check for symmetry applications during prover9's cnf construction
    where.find(_ equals what).isDefined
  }

  def introduceContractions(resp: LKProof, s: FClause): LKProof= {
   // for each formula F in s, count its occurrences in s and resp and apply contractions on resp until we reach the same number
   val p1 = s.neg.toSet.foldLeft(resp)((p,f) =>
       ((1).to(p.root.antecedent.filter(_.formula == f).size - s.neg.filter(_ == f).size)).foldLeft(p)((q,n) =>
        ContractionLeftRule(q,f.asInstanceOf[HOLFormula]) ))
   val p2 = s.pos.toSet.foldLeft(p1)((p,f) =>
       ((1).to(p.root.succedent.filter(_.formula == f).size - s.pos.filter(_ == f).size)).foldLeft(p)((q,n) =>
    ContractionRightRule(q,f.asInstanceOf[HOLFormula]) ))
   p2
  }

  /**
   * assuming a in CNF^-(f) we give a proof of a o |- f
   * @param f
   * @param a
   * @return
   */
  private def PCNFn(f: HOLFormula, a: FClause, sub: Substitution[HOLExpression]): LKProof = f match {
    case Atom(_,_) => Axiom(List(f),List(f))
    case Neg(f2) => NegRightRule(PCNFp(f2,a,sub), f2)
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
      AndRightRule(PCNFn(f1,a,sub), PCNFn(f2,a,sub), f1, f2)
    }
    case Or(f1,f2) =>
      if (containsSubsequent(CNFn(f1),as(a,sub))) OrRight1Rule(PCNFn(f1,a,sub),f1,f2)
      else if (containsSubsequent(CNFn(f2),as(a,sub))) OrRight2Rule(PCNFn(f2,a,sub),f1,f2)
      else throw new IllegalArgumentException("clause: " + as(a,sub) + " is not found in CNFs of ancestors: "
        +CNFn(f1) + " or " + CNFn(f2)+" of formula "+f)
    case Imp(f1,f2) => {
      if (containsSubsequent(CNFp(f1), as(a,sub))) ImpRightRule(WeakeningRightRule(PCNFp(f1,a,sub), f2), f1,f2)
      else if (containsSubsequent(CNFn(f2),as(a,sub))) ImpRightRule(WeakeningLeftRule(PCNFn(f2,a,sub), f1), f1, f2)
      else throw new IllegalArgumentException("clause: " + as(a,sub) + " is not found in CNFs of ancestors: "
        +CNFp(f1) + " or " + CNFn(f2)+" of formula "+f)
    }
    case ExVar(v,f2) => ExistsRightRule(PCNFn(f2, a,sub), f2 ,f, v.asInstanceOf[HOLVar])
    case _ => throw new IllegalArgumentException("unknown head of formula: " + a.toString)
  }

  /**
   * assuming a in CNF^+(f) we give a proof of a o f |-
   * @param f
   * @param a
   * @return
   */
  private def PCNFp(f: HOLFormula, a: FClause, sub: Substitution[HOLExpression]): LKProof = f match {
    case Atom(_,_) => Axiom(List(f),List(f))
    case Neg(f2) => NegLeftRule(PCNFn(f2,a,sub), f2)
    case And(f1,f2) =>
      if (containsSubsequent(CNFp(f1),as(a,sub))) AndLeft1Rule(PCNFp(f1,a,sub),f1,f2)
      else if (containsSubsequent(CNFp(f2),as(a,sub))) AndLeft2Rule(PCNFp(f2,a,sub),f1,f2)
      else throw new IllegalArgumentException("clause: " + as(a,sub) + " is not found in CNFs of ancestors: "
        +CNFp(f1) + " or " + CNFp(f2)+" of formula "+f)
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
      OrLeftRule(PCNFp(f1,a,sub), PCNFp(f2,a,sub), f1, f2)
    }
    case Imp(f1,f2) => {
      /*
      // get all possible partitions of the ant and suc of the clause a
      val prod = for ((c1,c2) <- power(a.neg.toList); (d1,d2) <- power(a.pos.toList)) yield (FClause(c1,d1),FClause(c2,d2))
      // find the right partition
      val cnf1 = CNFn(f1)
      val cnf2 = CNFp(f2)
      val par = prod.find(x => cnf1.contains(x._1) && cnf2.contains(x._2)).get
      // create the proof
      ImpLeftRule(PCNFn(f1,par._1), PCNFp(f2,par._2), f1, f2)
      */
      ImpLeftRule(PCNFn(f1,a,sub), PCNFp(f2,a,sub), f1, f2)
    }
    case AllVar(v,f2) => ForallLeftRule(PCNFp(f2, a,sub), f2, f, v.asInstanceOf[HOLVar])
    case _ => throw new IllegalArgumentException("unknown head of formula: " + a.toString)
  }

  def getVariableRenaming(f1: FClause, f2: FClause): Option[Substitution[HOLExpression]] = {
    if (f1.neg.size != f2.neg.size || f1.pos.size != f2.pos.size) None
    else {
      val pairs = (f1.neg.asInstanceOf[Seq[HOLExpression]].zip(f2.neg.asInstanceOf[Seq[HOLExpression]])
        ++ f1.pos.asInstanceOf[Seq[HOLExpression]].zip(f2.pos.asInstanceOf[Seq[HOLExpression]]))
      try {
        val sub = pairs.foldLeft(Substitution[HOLExpression]())((sb,p) =>
            sb simultaneousCompose computeSub(p))
        if (pairs.forall(p => sub(p._1) == p._2)) Some(sub) else None
      } catch {
        case e: Exception => None
      }
    }
  }
  def computeSub(p: Pair[HOLExpression,HOLExpression]): Substitution[HOLExpression] = (p._1, p._2) match {
    case (HOLVar(a,_), HOLVar(b,_)) if a == b =>Substitution[HOLExpression]()
    case (v1: HOLVar, v2: HOLVar) => Substitution(v1,v2)
    case (c1: HOLConst, c2: HOLConst) => Substitution[HOLExpression]()
    case (HOLApp(a1,b1),HOLApp(a2,b2)) =>
      computeSub((a1,a2)) simultaneousCompose computeSub(b1,b2)
    case (HOLAbs(v1,a1), HOLAbs(v2,a2)) => Substitution(computeSub(a1,a2).map - v1)
    case _ => throw new Exception()
  }

  // we need to compute (Not anymore)) the power set of the literals of the clause in order to find the right division of them in and right and or left
  def power[A](lst: List[A]): List[Tuple2[List[A],List[A]]] = {
    @annotation.tailrec
    def pwr(s: List[A], acc: List[Tuple2[List[A],List[A]]]): List[Tuple2[List[A],List[A]]] = s match {
      case Nil     => acc
      case a :: as => pwr(as, acc ::: (acc map (x => (a :: x._1,removeFirst(x._2,a).toList))))
    }
    pwr(lst, (Nil,lst) :: Nil)
  }

  def containsSubsequent(set : Set[FClause], fc : FClause) : Boolean = {
    val fs = fc.toFSequent
    //println("Checking "+fs)
    val r = set.filter( x => {/*println("... with "+x);*/ (x.toFSequent diff fs).isEmpty })
    r.nonEmpty
  }

  def removeFirst[A](s: Seq[A], a: A): Seq[A] = {
    val index = s.indexOf(a)
    s.take(index) ++ s.takeRight(s.size-index-1)
  }

  // applying sub to a clause
  def as(a: FClause, sub: Substitution[HOLExpression]): FClause = FClause(a.neg.map(f => sub(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]), a.pos.map(f =>
      sub(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]))
}

