
package at.logic.algorithms.resolution

import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol._
import at.logic.calculi.resolution.{FClause, Clause}
import at.logic.algorithms.lk.{applySubstitution => applySub, CleanStructuralRules, CloneLKProof}
import at.logic.language.hol.HOLFormula
import at.logic.utils.logging.Logger


object RobinsonToLK extends Logger {
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
    //val p = addWeakenings.weaken(ContractionMacroRule(recConvert(resproof, s, scala.collection.mutable.Map[FClause,LKProof](), memotable.getPCNF),s, strict = false), s)
    val p = WeakeningContractionMacroRule(recConvert(resproof, s, scala.collection.mutable.Map[FClause,LKProof](), memotable.getPCNF),s, strict = true)
    debug("Memoization saved "+memotable.getHits()+" calls!")
    p
  }

  // if the proof can be obtained from the CNF(-s) then we compute an LKProof of |- s
  def apply(resproof: RobinsonResolutionProof, s: FSequent, map: mapT): LKProof = {
    val memotable = new PCNFMemoTable(s)
    val p = WeakeningContractionMacroRule(recConvert(resproof, s, map, memotable.getPCNF),s, strict = false)
    debug("Memoization saved "+memotable.getHits()+" calls!")
    p
  }

  def apply(resproof: RobinsonResolutionProof): LKProof =
    recConvert(resproof, FSequent(List(),List()), scala.collection.mutable.Map[FClause,LKProof](),x => Axiom(x.neg, x.pos))

  // this contructor allows passing your own axiom creator e.g. for ceres projections
  def apply(resproof: RobinsonResolutionProof, s: FSequent, createAxiom : FClause => LKProof): LKProof =
    //addWeakenings.weaken(ContractionMacroRule(recConvert(resproof, s, scala.collection.mutable.Map[FClause,LKProof](), createAxiom),s, strict = false), s)
    WeakeningContractionMacroRule(recConvert(resproof, s, scala.collection.mutable.Map[FClause,LKProof](), createAxiom),s, strict = true)

  private def recConvert(proof: RobinsonResolutionProof, seq: FSequent, map: mapT, createAxiom : FClause => LKProof): LKProof = {
    if (map.contains(proof.root.toFClause)) {
      CloneLKProof(map(proof.root.toFClause))
    } else {
      val ret : LKProof = proof match {
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
          ContractionMacroRule(CutRule(u1, u2, s(a1.formula.asInstanceOf[FOLFormula]).asInstanceOf[FOLFormula]),seq, strict = false)
        }
        case Paramodulation(r, p1, p2, a1, a2, _, s) => {

          val u1 = applySub(recConvert(p1, seq,map,createAxiom),s)._1
          val u2 = applySub(recConvert(p2, seq,map,createAxiom),s)._1

          val Atom(_, s0 :: _) = a1.formula
          val s1 = s(s0.asInstanceOf[FOLExpression]).asInstanceOf[FOLTerm]

          // locate principal formula
          val lo = r.antecedent.find(_.parents.contains(a2))
          val ro = r.succedent.find(_.parents.contains(a2))
          // left rule
          val retProof = if (ro == None) {
            val lof = lo.get.formula.asInstanceOf[FOLFormula]
            // locate aux formulae
            val aux1 = u1.root.succedent.find(_.formula == s(a1.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
            val aux2 = u2.root.antecedent.find(_.formula == s(a2.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get

            if(isTrivial(aux1.formula, aux2.formula, lof)) {
              val newEndSequent = FSequent(u1.root.antecedent.map(_.formula) ++ u2.root.antecedent.map(_.formula),
                                           u1.root.succedent.filterNot(_ == aux1).map(_.formula) ++ u2.root.succedent.map(_.formula))
              println("This paramodulation is trivial.")
              WeakeningMacroRule(u2, newEndSequent)
            }
            else
              EquationLeftRule(u1, u2, aux1, aux2, lof)
          }
          // right rule
          else {
            val rof = ro.get.formula.asInstanceOf[FOLFormula]
            // locate aux formulae

            val aux1 = u1.root.succedent.find(_.formula == s(a1.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
            val aux2 = u2.root.succedent.find(_.formula == s(a2.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get

            if(isTrivial(aux1.formula, aux2.formula, rof)) {
              val newEndSequent = FSequent(u1.root.antecedent.map(_.formula) ++ u2.root.antecedent.map(_.formula),
                                           u1.root.succedent.filterNot(_ == aux1).map(_.formula) ++ u2.root.succedent.map(_.formula))
              println("This paramodulation is trivial.")
              WeakeningMacroRule(u2, newEndSequent)
            }
            else
            EquationRightRule(u1, u2, aux1, aux2, rof)
          }
          ContractionMacroRule(retProof, seq, strict = false)
        }
        // this case is applicable only if the proof is an instance of RobinsonProofWithInstance
        case Instance(root,p,s) =>
          debug("applying sub "+s+" to "+root)
          val rp = recConvert(p, seq,map,createAxiom)
          debug("lk proof root is "+rp.root)
          try {
            applySub(rp, s)._1
          } catch {
            case e@LKQuantifierException(root, occf, term, formula, qvar) =>
             throw new LKUnaryRuleCreationException("Substitution errror: "+s+":\n"+e.getMessage, rp, List(occf, formula))
            case e:Throwable =>
              throw new Exception("Unhandled error:"+e.getMessage, e)
          }
      }
      map(proof.root.toFClause) = ret
      ret
    }
  }

  /** Tests whether constructing an equality rule with a given equation, auxiliary formula and main formula would be superfluous.
   *
   * @param equation An Equation.
   * @param aux A HOLFormula.
   * @param main A HOLFormula.
   * @return True iff 1.) equation is of the form s = s 2,) main and aux coincide and 3.) s occurs in aux.
   */
  private def isTrivial(equation: HOLFormula, aux: HOLFormula, main: HOLFormula): Boolean = equation match {
    case Equation(s, t) =>
      if (s != t || aux != main)
        false
      else if (aux.find(s).isEmpty)
        throw new Exception("Bad paramodulation: equation "+equation+", aux formula "+aux+", main formula"+main)
      else
        true
    case _ => throw new Exception(equation+" is not an equation.")
  }

}
