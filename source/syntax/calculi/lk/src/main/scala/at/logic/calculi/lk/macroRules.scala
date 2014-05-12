/*
 * macroRules.scala
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.fol.{Neg => FOLNeg, Or => FOLOr, And => FOLAnd, Imp => FOLImp, Atom => FOLAtom, AllVar => FOLAllVar, Equation => FOLEquation, instantiateAll}
import at.logic.language.fol.{FOLVar, FOLTerm, FOLFormula}
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.utils.ds.trees._
import base._

  /** <pre>Replaces a formulas A, B (marked by term1oc & term2oc) with the conjunction
    * A ^ B in the antecedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    *     sL, A, B |- sR
    * ------------------- (AndLeft)
    * sL, A ^ B |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, A, B |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of A in the antecedent of s1.
    * @param term2oc The occurrence of B in the antecedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
object AndLeftRule {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val p0 = AndLeft1Rule( s1, term1oc, term2oc.formula.asInstanceOf[HOLFormula] )
    val p1 = AndLeft2Rule( p0, term1oc.formula.asInstanceOf[HOLFormula], p0.getDescendantInLowerSequent( term2oc ).get )
    ContractionLeftRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
  }

  /** <pre>Replaces a formulas term1, term2 with the conjunction
    * term1 ^ term2 in the antecedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    * sL, term1, term2 |- sR
    * ---------------------- (AndLeft)
    * sL, term1 ^ term2 |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, term1, term2 |- sR) as the bottommost sequent.
    * @param term1 The first formula to be replaced in the antecedent of s1.
    * @param term2 The second formula to be replaced in the antecedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    val x1 = s1.root.antecedent.find( _.formula == term1 )
    if (x1 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    val x2 = s1.root.antecedent.find( x => x.formula == term2 && x != x1.get )
    if (x2 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    apply(s1, x1.get, x2.get)
  }
}

object OrRightRule {

  /** <pre>Replaces a formulas A, B (marked by term1oc & term2oc) with the disjunction
    * A v B in the succedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    *   sL|- sR, A, B
    * ------------------- (OrRight)
    * sL |- sR, A v B
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, A, B) as the bottommost sequent.
    * @param term1oc The occurrence of A in the succedent of s1.
    * @param term2oc The occurrence of B in the succedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val p0 = OrRight1Rule( s1, term1oc, term2oc.formula )
    val p1 = OrRight2Rule( p0, term1oc.formula, p0.getDescendantInLowerSequent( term2oc ).get )
    ContractionRightRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
  }

  /** <pre>Replaces a formulas term1, term2 with the disjunction
    * term1 v term2 in the succedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    * sL |- sR, term1, term2
    * ---------------------- (OrRight)
    * sL |- sR, term1 v term2
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, term1, term2) as the bottommost sequent.
    * @param term1 The first formula to be replaced in the succedent of s1.
    * @param term2 The second formula to be replaced in the succedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    val x1 = s1.root.succedent.find( _.formula == term1 )
    if (x1 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    val x2 = s1.root.succedent.find( x => x.formula == term2 && x != x1.get )
    if (x2 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    apply(s1, x1.get, x2.get)
  }
}

  object TransRule {
    /** <pre>Performs a proof employing transitivity.
      *
      * Takes a proof s2 with end-sequent of the form
      * (x=z), Trans, ... |- ...
      * and return one with end-sequent of the form
      * (x=y), (y=z), Trans, ... |- ...
      * where Trans is defined as Forall xyz.((x=y ^ y=z) -> x=z)
      * </pre>
      * @param x X
      * @param y Y
      * @param z Z
      * @param s2 The proof which contains the (x=z) which is to be shown.
      * @return A proof wich s2 as a subtree and the formula (x=z) replaced by (x=y) and (y=z).
      */
    def apply (x: FOLTerm, y: FOLTerm, z: FOLTerm, s2: LKProof) : LKProof = {

      val xv = FOLVar(StringSymbol("x"))
      val yv = FOLVar(StringSymbol("y"))
      val zv = FOLVar(StringSymbol("z"))

      //Forall xyz.(x = y ^ y = z -> x = z)
      val Trans = FOLAllVar(xv, FOLAllVar(yv, FOLAllVar(zv, FOLImp(FOLAnd(FOLEquation( xv, yv) , FOLEquation( yv, zv) ), FOLEquation( xv, zv)))))
      def TransX(x:FOLTerm) = FOLAllVar(yv, FOLAllVar(zv, FOLImp(FOLAnd(FOLEquation( x, yv) , FOLEquation( yv, zv) ), FOLEquation( x, zv))))
      def TransXY(x:FOLTerm, y:FOLTerm) = FOLAllVar(zv, FOLImp(FOLAnd(FOLEquation( x, y) , FOLEquation( y, zv) ), FOLEquation( x, zv)))
      def TransXYZ(x:FOLTerm, y: FOLTerm, z:FOLTerm) = FOLImp(FOLAnd(FOLEquation( x, y) , FOLEquation( y, z) ), FOLEquation( x, z))

      val xy = FOLEquation( x, y)
      val yz = FOLEquation( y, z)
      val xz = FOLEquation( x, z)

      val ax_xy = Axiom(xy::Nil, xy::Nil)
      val ax_yz = Axiom(yz::Nil, yz::Nil)

      val s1 = AndRightRule(ax_xy, ax_yz, xy, yz)

      val imp = ImpLeftRule(s1, s2, FOLAnd(xy, yz), xz)

      val allQZ = ForallLeftRule(imp, TransXYZ(x, y, z) , TransXY(x, y), z)
      val allQYZ = ForallLeftRule(allQZ, TransXY(x,y), TransX(x), y)
      val allQXYZ = ForallLeftRule(allQYZ, TransX(x), Trans, x)

      ContractionLeftRule(allQXYZ, Trans)
    }
  }

  object ForallLeftBlock {
    /** <pre>Applies the ForallLeft-rule n times.
      * This method expects a formula main with
      * a quantifier block, and a proof s1 which has a fully
      * instantiated version of main on the left side of its
      * bottommost sequent.
      *
      * The rule: 
      *   (rest of s1)
      *  sL, A[x1\term1,...,xN\termN] |- sR
      * ---------------------------------- (ForallLeft x n)
      *     sL, Forall x1,..,xN.A |- sR
      * </pre>
      *
      * @params s1 The top proof with (sL, A[x1\term1,...,xN\termN] |- sR) as the bocttommost sequent.
      * @params main A formula of the form (Forall x1,...,xN.A).
      * @params terms The list of terms with which to instantiate main. The caller of this
      * method has to ensure the correctness of these terms, and, specifically, that
      * A[x1\term1,...,xN\termN] indeed occurs at the bottom of the proof s1.
      */
    def apply(s1: LKProof, main: FOLFormula, terms:List[FOLTerm]) : LKProof = {
      val partiallyInstantiatedMains = (0 to terms.length).toList.reverse.map(n => instantiateAll(main, terms.take(n))).toList

      //partiallyInstantiatedMains.foreach(println)

      val series = terms.reverse.foldLeft((s1,partiallyInstantiatedMains)){(acc, ai) =>
        /*println("MACRORULES|FORALLLEFTBLOCK|APPLYING FORALLEFT")
        println("s1: " + acc._1)
        println("aux: " + acc._2.head)
        println("main: " + acc._2.tail.head)
        println("term: " + ai)*/
        (ForallLeftRule(acc._1, acc._2.head, acc._2.tail.head, ai), acc._2.tail)
      }

      series._1
    }
  }

  object ForallRightBlock {
    /** <pre>Applies the ForallRight-rule n times.
      * This method expects a formula main with
      * a quantifier block, and a proof s1 which has a fully
      * instantiated version of main on the right side of its
      * bottommost sequent.
      *
      * The rule: 
      *   (rest of s1)
      *  sL |- sR, A[x1\y1,...,xN\yN]
      * ---------------------------------- (ForallRight x n)
      *     sL |- sR, Forall x1,..,xN.A
      *
      * where y1,...,yN are eigenvariables.
      * </pre>
      *
      * @params s1 The top proof with (sL |- sR, A[x1\y1,...,xN\yN]) as the bocttommost sequent.
      * @params main A formula of the form (Forall x1,...,xN.A).
      * @params terms The list of eigenvariables with which to instantiate main. The caller of this
      * method has to ensure the correctness of these terms, and, specifically, that
      * A[x1\y1,...,xN\yN] indeed occurs at the bottom of the proof s1.
      */
    def apply(s1: LKProof, main: FOLFormula, eigenvariables:List[FOLVar]) : LKProof = {
      val partiallyInstantiatedMains = (0 to eigenvariables.length).toList.reverse.map(n => instantiateAll(main, eigenvariables.take(n))).toList

      //partiallyInstantiatedMains.foreach(println)

      val series = eigenvariables.reverse.foldLeft((s1,partiallyInstantiatedMains)){(acc, ai) =>
        /*println("MACRORULES|FORALLRIGHTBLOCK|APPLYING FORALLEFT")
        println("s1: " + acc._1)
        println("aux: " + acc._2.head)
        println("main: " + acc._2.tail.head)
        println("term: " + ai)*/
        (ForallRightRule(acc._1, acc._2.head, acc._2.tail.head, ai), acc._2.tail)
      }

      series._1
    }
  }

