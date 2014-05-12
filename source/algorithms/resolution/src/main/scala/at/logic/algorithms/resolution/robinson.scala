
package at.logic.algorithms.resolution

import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol._
import at.logic.calculi.resolution.{FClause, Clause}
import at.logic.algorithms.lk.{applySubstitution => applySub, addWeakenings, CleanStructuralRules, CloneLKProof}


object RobinsonToLK {
  type mapT = scala.collection.mutable.Map[FClause,LKProof]

  //encapsulates a memo table s.t. subsequent runs of PCNF are not computed multiple times for the same c
  private class PCNFMemoTable(val endsequent : FSequent) {
    val table : mapT = scala.collection.mutable.Map[FClause,LKProof]()
    var hits : Int = 0

    def getHits() = this.hits

    def getPCNF(c : FClause) = {
      if (! (table contains c)) {
        table.put(c,PCNF(endsequent,c))
      } else {
        hits = hits +1
      }
      table(c)
    }
  }

  //def fol2hol(s: Substitution[FOLExpression]):Substitution[HOLExpression] = s.asInstanceOf[Substitution[HOLExpression]]

  // if the proof can be obtained from the CNF(-s) then we compute an LKProof of |- s
  def apply(resproof: RobinsonResolutionProof, s: FSequent): LKProof = {
    val memotable = new PCNFMemoTable(s)
    val p = addWeakenings.weaken(introduceContractions(recConvert(resproof, s, scala.collection.mutable.Map[FClause,LKProof](), memotable.getPCNF),s), s)
    println("Memoization saved "+memotable.getHits()+" calls!")
    p
  }

  // if the proof can be obtained from the CNF(-s) then we compute an LKProof of |- s
  def apply(resproof: RobinsonResolutionProof, s: FSequent, map: mapT): LKProof = {
    val memotable = new PCNFMemoTable(s)
    val p = addWeakenings.weaken(introduceContractions(recConvert(resproof, s, map, memotable.getPCNF),s), s)
    println("Memoization saved "+memotable.getHits()+" calls!")
    p
  }

  def apply(resproof: RobinsonResolutionProof): LKProof =
    recConvert(resproof, FSequent(List(),List()), scala.collection.mutable.Map[FClause,LKProof](),x => Axiom(x.neg, x.pos))

  // this contructor allows passing your own axiom creator e.g. for ceres projections
  def apply(resproof: RobinsonResolutionProof, s: FSequent, createAxiom : FClause => LKProof): LKProof =
    addWeakenings.weaken(introduceContractions(recConvert(resproof, s, scala.collection.mutable.Map[FClause,LKProof](), createAxiom),s), s)


  /**
   * apply contractions so, when considering the literals of both s and the end sequent of resp as multisets,  s is a sub-multiset of the
   * end sequent
   */
  def introduceContractions(resp: LKProof, s: FSequent): LKProof= {
    // for each formula F in s, count its occurrences in s and resp and apply contractions on resp until we reach the same number
    val p1 = s.antecedent.toSet.foldLeft(resp)((p,f) =>
      ((1).to(p.root.antecedent.filter(_.formula == f).size - s.antecedent.filter(_ == f).size)).foldLeft(p)((q,n) =>
        ContractionLeftRule(q,f) ))
    val p2 = s.succedent.toSet.foldLeft(p1)((p,f) =>
      ((1).to(p.root.succedent.filter(_.formula == f).size - s.succedent.filter(_ == f).size)).foldLeft(p)((q,n) =>
        ContractionRightRule(q,f) ))
    p2
  }

  private def recConvert(proof: RobinsonResolutionProof, seq: FSequent, map: mapT, createAxiom : FClause => LKProof): LKProof = {
    if (map.contains(proof.root.toFClause)) {
      CloneLKProof(map(proof.root.toFClause))
    } else {
      val ret = proof match {
        case InitialClause(cls) => //
        // if (seq.antecedent.isEmpty && seq.succedent.isEmpty)
        // Axiom(cls.negative.map(_.formula), cls.positive.map(_.formula))
        // use projections
        //else PCNF(seq, cls.toFClause)
          createAxiom(cls.toFClause)
        case Factor(r, p, a, s) => {
          // obtain the set of removed occurrences for each side
          val (leftContracted, rightContracted) =
            if (a.size ==1)
              if (p.root.antecedent.contains(a(0).head)) (a(0).tail, Nil)
              else (Nil, a(0).tail)
            else
            if (a.size ==2)
              if (p.root.antecedent.contains(a(0).head)) (a(0).tail, a(1).tail)
              else (a(1).tail, a(0).tail)
            else throw new Exception("Unexpected number of auxiliary formulas!")

          // obtain upper proof recursively and apply the current substitution to the resulted LK proof
          var res = applySub(recConvert(p,seq,map,createAxiom), s)._1

          // create a contraction for each side, for each contracted formula with a._1 and a._2 (if exists)
          // note that sub must be applied to all formulas in the lk proof
          // var hasLeft = false
          if (!leftContracted.isEmpty) {
            // val leftAux = a(0) since we do not compare occurrences but only formulas and all formulas are identical in LK contraction, we can ignore this value
            // hasLeft = true
            res = leftContracted.foldLeft(res)((p, fo) => ContractionLeftRule(
              p, s(fo.formula)))
          }
          if (!rightContracted.isEmpty) {
            // val rightAux = if (hasLeft) a(1) else a(0)
            res = rightContracted.foldLeft(res)((p, fo) => ContractionRightRule(
              p, s(fo.formula)))
          }
          res
        }
        case Variant(r, p, s) => applySub(recConvert(p, seq,map,createAxiom), s)._1 // the construction of an LK proof makes sure we create a tree out of the agraph
        case Resolution(r, p1, p2, a1, a2, s) => {
          val u1 = applySub(recConvert(p1, seq,map,createAxiom),s)._1
          val u2 = applySub(recConvert(p2, seq,map,createAxiom),s)._1
          introduceContractions(CutRule(u1, u2, s(a1.formula.asInstanceOf[FOLFormula]).asInstanceOf[FOLFormula]),seq)
        }
        case Paramodulation(r, p1, p2, a1, a2, _, s) => {

          val u1 = applySub(recConvert(p1, seq,map,createAxiom),s)._1
          val u2 = applySub(recConvert(p2, seq,map,createAxiom),s)._1

          val Atom(_, s0 :: _) = a1.formula
          val s1 = s(s0.asInstanceOf[FOLExpression]).asInstanceOf[FOLTerm]

          // locate principal formula
          val lo = r.antecedent.find(_.ancestors.contains(a2))
          val ro = r.succedent.find(_.ancestors.contains(a2))
          // left rule
          val retProof = if (ro == None) {
            val lof = lo.get.formula.asInstanceOf[FOLFormula]
            // locate aux formulae
            val aux1 = u1.root.succedent.find(_.formula == s(a1.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
            val aux2 = u2.root.antecedent.find(_.formula == s(a2.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
            // rule 1
            if (isRule1(lof, aux2.formula.asInstanceOf[FOLFormula], s1)) EquationLeft1Rule(u1, u2, aux1, aux2, lof)
            // rule 2
            else EquationLeft2Rule(u1, u2, aux1, aux2, lof)
          }
          // right rule
          else {
            val rof = ro.get.formula.asInstanceOf[FOLFormula]
            // locate aux formulae

            val aux1 = u1.root.succedent.find(_.formula == s(a1.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
            val aux2 = u2.root.succedent.find(_.formula == s(a2.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
            // rule 1
            if (isRule1(rof, aux2.formula.asInstanceOf[FOLFormula], s1)) EquationRight1Rule(u1, u2, aux1, aux2, rof)
            // rule 2
            else EquationRight2Rule(u1, u2, aux1, aux2, rof)
          }
          introduceContractions(retProof, seq)
        }
        // this case is applicable only if the proof is an instance of RobinsonProofWithInstance
        case Instance(_,p,s) =>
          applySub(recConvert(p, seq,map,createAxiom),s)._1
      }
      map(proof.root.toFClause) = ret
      ret
    }
  }

  // in order to distinguish between rule 1 and rule 2 in equation rules we search for the substituted formula in the obtained one
  // if f2 contains more occurrences of the sub term than f1 then it means that this subterm was replaced by something else
  private def isRule1(f1: FOLFormula, f2: FOLFormula, t: FOLTerm): Boolean = (countSB(f2, t) > countSB(f1, t))

  private def countSB(t1: FOLExpression, t2: FOLExpression): Int =
    if (t1 == t2) 1
    else t1 match {
      case FOLVar(_) => 0
      case FOLConst(_) => 0
      case Atom(_, args) => args.foldLeft(0)((n, arg) => n + countSB(arg, t2))
      case Function(_, args) => args.foldLeft(0)((n, arg) => n + countSB(arg, t2))
    }
}
