/*
 * StillmanSubsumptionAlgorithm.scala
 *
 */

package at.logic.algorithms.subsumption

import at.logic.algorithms.matching._
import at.logic.language.hol.{HOLExpression, Substitution => SubstitutionHOL, Neg => NegHOL, HOLVar, freeVariables => freeVariablesHOL, rename => renameHOL}
import at.logic.language.fol.{FOLFormula, FOLExpression, Substitution => SubstitutionFOL, Neg => NegFOL, FOLVar, freeVariables => freeVariablesFOL, rename => renameFOL}
import at.logic.calculi.lk.base.FSequent
import at.logic.utils.dssupport.ListSupport.remove_doubles

// TODO: find a smart way (without reaching out to the lambda layer!!) to not duplicate this code.

object StillmanSubsumptionAlgorithmHOL extends SubsumptionAlgorithm {
  val matchAlg = NaiveIncompleteMatchingAlgorithm

  def subsumes(s1: FSequent, s2: FSequent): Boolean = subsumes_by(s1,s2).nonEmpty

  /**
   * Calculates the subtitution to apply to s1 in order to subsume s2. if it exists
   * @param s1 a clause
   * @param s2 a clause
   * @return if s1 subsumes s2, the substitution necessary. None otherwise.
   */
  def subsumes_by(s1: FSequent, s2: FSequent) : Option[SubstitutionHOL] = {
    val left = s1._1.map(x => NegHOL(x)) ++ s1._2.map(x => x)
    val right = s2._1.map(x => NegHOL(x)) ++ s2._2.map(x => x)
    val lv = remove_doubles(left.foldLeft(List[HOLVar]())((l,f) => freeVariablesHOL(f) ++ l))
    val rv = remove_doubles(right.foldLeft(List[HOLVar]())((l,f) => freeVariablesHOL(f) ++ l))
    val renames = rv.filter(x=> lv.contains(x))
    val (newnames, _) = renames.reverse.foldLeft((List[HOLVar](), lv++rv))((pair,x) => {
      val v = renameHOL(x, pair._2)
      require(v.exptype == x.exptype, "Error renaming variable! Old type "+x.exptype+" != new type "+v.exptype)
      (v::pair._1, v::pair._2)
    }  )

    val sub = SubstitutionHOL(renames zip newnames)
    val rsub = SubstitutionHOL(newnames zip renames)

    ST(left, right.map(f => sub(f)), SubstitutionHOL(), newnames) match {
      case None => None
      case Some(subst) => Some(SubstitutionHOL(subst.holmap.map(x => (x._1, rsub(x._2)))))
    }
  } 
  
  def ST(ls1: Seq[HOLExpression], ls2: Seq[HOLExpression], sub: SubstitutionHOL, restrictedDomain: List[HOLVar])
   : Option[SubstitutionHOL] =
    ls1 match {
      case Nil => Some(sub) // first list is exhausted
      case x::ls =>
        val sx = sub(x);
        //TODO: the original algorithm uses backtracking, this does not. check if this implementation is incomplete
        val nsubs = ls2.flatMap(t =>
          matchAlg.matchTerm(sx, sub(t), restrictedDomain) match {
            case Some(sub2) =>
              val nsub = sub2.compose(sub)
              val st = ST(ls, ls2, nsub, restrictedDomain ++ nsub.holmap.flatMap(s => freeVariablesHOL(s._2)))
              if (st.nonEmpty) st::Nil else Nil
            case _ => Nil
      })
      if (nsubs.nonEmpty) nsubs.head else None
  }
}

object StillmanSubsumptionAlgorithmFOL extends SubsumptionAlgorithm {
  val matchAlg = FOLMatchingAlgorithm
  
  def subsumes(s1: FSequent, s2: FSequent): Boolean = subsumes_by(s1,s2).nonEmpty
 
  def subsumes_by(s1: FSequent, s2: FSequent) : Option[SubstitutionFOL] = {
    val left = s1._1.map(x => NegFOL(x.asInstanceOf[FOLFormula])) ++ s1._2.map(x => x.asInstanceOf[FOLFormula])
    val right = s2._1.map(x => NegFOL(x.asInstanceOf[FOLFormula])) ++ s2._2.map(x => x.asInstanceOf[FOLFormula])
    val lv = remove_doubles(left.foldLeft(List[FOLVar]())((l,f) => freeVariablesFOL(f) ++ l))
    val rv = remove_doubles(right.foldLeft(List[FOLVar]())((l,f) => freeVariablesFOL(f) ++ l))
    val renames = rv.filter(x=> lv.contains(x))
    val (newnames, _) = renames.foldLeft((List[FOLVar](), lv++rv))((pair,x) => {
      val v = renameFOL(x, pair._2)
      (v::pair._1, v::pair._2)
    }  )

    val sub = SubstitutionFOL(renames zip newnames)
    val rsub = SubstitutionFOL(newnames zip renames)

    ST(left, right.map(f => sub(f)), SubstitutionFOL(), newnames) match {
      case None => None
      case Some(subst) => Some(SubstitutionFOL(subst.folmap.map(x => (x._1, rsub(x._2)))))
    }
  } 
 
  def ST(ls1: Seq[FOLExpression], ls2: Seq[FOLExpression], sub: SubstitutionFOL, restrictedDomain: List[FOLVar]) 
   : Option[SubstitutionFOL] = ls1 match {
    case Nil => Some(sub) // first list is exhausted
    case x::ls => 
      val sx = sub(x); 
      val nsubs = ls2.flatMap(t => 
        matchAlg.matchTerm(sx, sub(t), restrictedDomain) match {
          case Some(sub2) =>
            val nsub = sub2.compose(sub)
            val st = ST(ls, ls2, nsub, restrictedDomain ++ nsub.folmap.flatMap(s => freeVariablesFOL(s._2)))
            if (st.nonEmpty) st::Nil else Nil
          case _ => Nil
      })
      if (nsubs.nonEmpty) nsubs.head else None
  }
}

