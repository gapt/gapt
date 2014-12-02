/*
 * macroRules.scala
 */

package at.logic.calculi.lk

import at.logic.calculi.lk.EquationLeftBulkRule._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.fol.{Neg => FOLNeg, Or => FOLOr, And => FOLAnd, Imp => FOLImp, Atom => FOLAtom, AllVar => FOLAllVar, Equation => FOLEquation, instantiateAll}
import at.logic.language.fol.{FOLVar, FOLTerm, FOLFormula}
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.utils.ds.trees._
import at.logic.calculi.lk.base._
import scala.collection.mutable.ListBuffer

object AndLeftRule {
  /** <pre>Replaces a formulas A, B (marked by term1oc & term2oc) with the conjunction
    * A ∧ B in the antecedent of a sequent.
    * 
    * The rule: 
    *     (rest of s1)
    *     sL, A, B |- sR
    * ------------------- (AndLeft)
    * sL, A ∧ B |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, A, B |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of A in the antecedent of s1.
    * @param term2oc The occurrence of B in the antecedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val p0 = AndLeft1Rule( s1, term1oc, term2oc.formula.asInstanceOf[HOLFormula] )
    val p1 = AndLeft2Rule( p0, term1oc.formula.asInstanceOf[HOLFormula], p0.getDescendantInLowerSequent( term2oc ).get )
    ContractionLeftRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
  }

  /** <pre>Replaces a formulas term1, term2 with the conjunction
    * term1 ∧ term2 in the antecedent of a sequent.
    * 
    * The rule: 
    *     (rest of s1)
    * sL, term1, term2 |- sR
    * ---------------------- (AndLeft)
    * sL, term1 ∧ term2 |- sR
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
    * A ∨ B in the succedent of a sequent.
    * 
    * The rule: 
    *     (rest of s1)
    *   sL|- sR, A, B
    * ------------------- (OrRight)
    * sL |- sR, A ∨ B
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
    * term1 ∨ term2 in the succedent of a sequent.
    * 
    * The rule: 
    *     (rest of s1)
    * sL |- sR, term1, term2
    * ---------------------- (OrRight)
    * sL |- sR, term1 ∨ term2
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
      * where Trans is defined as Forall xyz.((x=y ∧ y=z) -> x=z)
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
      * @param s1 The top proof with (sL, A[x1\term1,...,xN\termN] |- sR) as the bocttommost sequent.
      * @param main A formula of the form (Forall x1,...,xN.A).
      * @param terms The list of terms with which to instantiate main. The caller of this
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
      * @param s1 The top proof with (sL |- sR, A[x1\y1,...,xN\yN]) as the bocttommost sequent.
      * @param main A formula of the form (Forall x1,...,xN.A).
      * @param eigenvariables The list of eigenvariables with which to instantiate main. The caller of this
      * method has to ensure the correctness of these terms, and, specifically, that
      * A[x1\y1,...,xN\yN] indeed occurs at the bottom of the proof s1.
      */
    def apply(s1: LKProof, main: FOLFormula, eigenvariables:List[FOLVar]) : LKProof = {
      val partiallyInstantiatedMains = (0 to eigenvariables.length).toList.reverse.map(n => instantiateAll(main, eigenvariables.take(n))).toList

      //partiallyInstantiatedMains.foreach(println)

      val series = eigenvariables.reverse.foldLeft((s1, partiallyInstantiatedMains)) { (acc, ai) =>
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

/** This macro rule unifies [[EquationLeft1Rule]] and [[EquationLeft2Rule]] by automatically choosing the appropriate rule.
 * 
 */
object EquationLeftRule extends EquationRuleLogger {

  /** 
   * 
   * @param s1 A proof ending with term1oc in the succedent.
   * @param s2 A proof ending with term2oc in the antecedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param pos A position such that A(pos) = s or A(pos) = t 
   * @return A proof ending with either an [[EquationLeft1Rule]] or an [[EquationLeft2Rule]] according to which replacement is sensible. 
   */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val eq = eqocc.formula

    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val aux = auxocc.formula
        val term = aux.get(pos)

        term match {
          case Some(`s`) => EquationLeft1Rule(s1, s2, term1oc, term2oc, pos)

          case Some(`t`) => EquationLeft2Rule(s1, s2, term1oc, term2oc, pos)

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /**
   * 
   * @param s1 A proof ending with term1oc in the succedent.
   * @param s2 A proof ending with term2oc in the antecedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param main A formula A' such that A' is obtained by replacing one occurrence of s in A by t or vice versa.
   * @return A proof ending with either an [[EquationLeft1Rule]] or an [[EquationLeft2Rule]] according to which one leads from A to A'.
   */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (s == t && aux == main) {
          warn("Producing equation rule with trivial equation.")
          EquationLeft1Rule(s1, s2, term1oc, term2oc, main)
        }

        else if (s == t && aux != main) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val sAux = aux.find(s)
          val sMain = main.find(s)

          val tAux = aux.find(t)
          val tMain = main.find(t)

          if (sAux.isEmpty && tAux.isEmpty)
            throw new LKRuleCreationException("Neither " + s + " nor " + t + " found in formula " + aux + ".")

          trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")

          val tToS = sMain intersect tAux
          val sToT = tMain intersect sAux
          trace("tToS = " + tToS)
          trace("sToT = " + sToT)

          if (sToT.length == 1 && tToS.length == 0) {
            val p = sToT.head
            val mainNew = HOLPosition.replace(aux, p, t)
            if (mainNew == main) {
              EquationLeft1Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
          }
          else if (tToS.length == 1 && sToT.length == 0) {
            val p = tToS.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              EquationLeft2Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Formulas " + aux + " and " + main + " don't differ in exactly one position.\n Equation: " + eqocc.formula)
        }
      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

  /**
   *
   * @param s1 A sequent with term1oc in the succedent.
   * @param s2 A sequent with term2oc in the antecedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param main A formula A' such that A' is obtained by replacing one occurrence of s in A by t or vice versa.
   * @return A proof ending with either an [[EquationLeft1Rule]] or an [[EquationLeft2Rule]] according to which one leads from A to A'.
   */
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (s == t && aux == main) {
          warn("Producing equation rule with trivial equation.")
          EquationLeft1Rule(s1, s2, term1oc, term2oc, main)
        }

        else if (s == t && aux != main) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }


        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val sAux = aux.find(s)
          val sMain = main.find(s)

          val tAux = aux.find(t)
          val tMain = main.find(t)

          if (sAux.isEmpty && tAux.isEmpty)
            throw new LKRuleCreationException("Neither " + s + " nor " + t + " found in formula " + aux + ".")

          trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")

          val tToS = sMain intersect tAux
          val sToT = tMain intersect sAux
          trace("tToS = " + tToS)
          trace("sToT = " + sToT)

          if (sToT.length == 1 && tToS.length == 0) {
            val p = sToT.head
            val mainNew = HOLPosition.replace(aux, p, t)
            if (mainNew == main) {
              EquationLeft1Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
          }
          else if (tToS.length == 1 && sToT.length == 0) {
            val p = tToS.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              EquationLeft2Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Formulas " + aux + " and " + main + " don't differ in exactly one position.\n Equation: " + eqocc.formula)
        }

      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

  /**
   *
   * @param s1 A sequent with term1oc in the succedent.
   * @param s2 A sequent with term2oc in the antecedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param pos A position such that A(pos) = s or A(pos) = t 
   * @return A proof ending with either an [[EquationLeft1Rule]] or an [[EquationLeft2Rule]] according to which replacement is sensible. 
   */
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val eq = eqocc.formula

    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val aux = auxocc.formula
        val term = aux.get(pos)

        term match {
          case Some(`s`) => EquationLeft1Rule(s1, s2, term1oc, term2oc, pos)

          case Some(`t`) => EquationLeft2Rule(s1, s2, term1oc, term2oc, pos)

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /** This version of the rule operates on formulas instead of occurrences. It will attempt to find appropriate occurrences in the premises.
    *
    * @param s1 A proof ending with term1oc in the succedent.
    * @param s2 A proof ending with term2oc in the antecedent.
    * @param term1 An equation s = t.
    * @param term2 A formula A.
    * @param main A formula A' such that A' is obtained by replacing one occurrence of s in A by t or vice versa.
    * @return A proof ending with either an [[EquationLeft1Rule]] or an [[EquationLeft2Rule]] according to which one leads from A to A'.
    */
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    (s1.root.succedent.filter(x => x.formula == term1).toList, s2.root.antecedent.filter(x => x.formula == term2).toList) match {
      case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    }
  }

  private def getTerms(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    val term2op = s2.antecedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    else {
      val eqocc = term1op.get
      val auxocc = term2op.get
      (eqocc, auxocc)
    }
  }
}

/** This macro rule unifies [[EquationRight1Rule]] and [[EquationRight2Rule]] by automatically choosing the appropriate rule.
  *
  */
object EquationRightRule extends EquationRuleLogger {

  /**
   *
   * @param s1 A proof ending with term1oc in the succedent.
   * @param s2 A proof ending with term2oc in the succedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param pos A position such that A(pos) = s or A(pos) = t 
   * @return A proof ending with either an [[EquationRight1Rule]] or an [[EquationRight2Rule]] according to which replacement is sensible. 
   */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val eq = eqocc.formula

    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val aux = auxocc.formula
        val term = aux.get(pos)

        term match {
          case Some(`s`) => EquationRight1Rule(s1, s2, term1oc, term2oc, pos)

          case Some(`t`) => EquationRight2Rule(s1, s2, term1oc, term2oc, pos)

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /**
   *
   * @param s1 A proof ending with term1oc in the succedent.
   * @param s2 A proof ending with term2oc in the succedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param main A formula A' such that A' is obtained by replacing one occurrence of s in A by t or vice versa.
   * @return A proof ending with either an [[EquationRight1Rule]] or an [[EquationRight2Rule]] according to which one leads from A to A'.
   */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " + s + " = " + t + ".")

        if (s == t && aux == main) {
          warn("Producing equation rule with trivial equation.")
          EquationRight1Rule(s1, s2, term1oc, term2oc, main)
        }

        else if (s == t && aux != main) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }


        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val sAux = aux.find(s)
          val sMain = main.find(s)

          val tAux = aux.find(t)
          val tMain = main.find(t)

          if (sAux.isEmpty && tAux.isEmpty)
            throw new LKRuleCreationException("Neither " + s + " nor " + t + " found in formula " + aux + ".")

          trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")

          val tToS = sMain intersect tAux
          val sToT = tMain intersect sAux
          trace("tToS = " + tToS)
          trace("sToT = " + sToT)

          if (sToT.length == 1 && tToS.length == 0) {
            val p = sToT.head
            val mainNew = HOLPosition.replace(aux, p, t)
            if (mainNew == main) {
              EquationRight1Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
          }
          else if (tToS.length == 1 && sToT.length == 0) {
            val p = tToS.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              EquationRight2Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Formulas " + aux + " and " + main + " don't differ in exactly one position.\n Equation: " + eqocc.formula)
        }
      case _ => throw new LKRuleCreationException("Formula " + eq + " is not an equation.")
    }
  }

  /**
   *
   * @param s1 A sequent with term1oc in the succedent.
   * @param s2 A sequent with term2oc in the succedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param main A formula A' such that A' is obtained by replacing one occurrence of s in A by t or vice versa.
   * @return A proof ending with either an [[EquationRight1Rule]] or an [[EquationRight2Rule]] according to which one leads from A to A'.
   */
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " + s + " = " + t + ".")

        if (s == t && aux == main) {
          warn("Producing equation rule with trivial equation.")
          EquationRight1Rule(s1, s2, term1oc, term2oc, main)
        }

        else if (s == t && aux != main) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val sAux = aux.find(s)
          val sMain = main.find(s)

          val tAux = aux.find(t)
          val tMain = main.find(t)

          if (sAux.isEmpty && tAux.isEmpty)
            throw new LKRuleCreationException("Neither " + s + " nor " + t + " found in formula " + aux + ".")

          trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")

          val tToS = sMain intersect tAux
          val sToT = tMain intersect sAux
          trace("tToS = " + tToS)
          trace("sToT = " + sToT)

          if (sToT.length == 1 && tToS.length == 0) {
            val p = sToT.head
            val mainNew = HOLPosition.replace(aux, p, t)
            if (mainNew == main) {
              EquationRight1Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
          }
          else if (tToS.length == 1 && sToT.length == 0) {
            val p = tToS.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              EquationRight2Rule(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Formulas " + aux + " and " + main + " don't differ in exactly one position.\n Equation: " + eqocc.formula)
        }
      case _ => throw new LKRuleCreationException("Formula " + eq + " is not an equation.")
    }
  }
  
  /**
   *
   * @param s1 A sequent with term1oc in the succedent.
   * @param s2 A sequent with term2oc in the succedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param pos A position such that A(pos) = s or A(pos) = t 
   * @return A proof ending with either an [[EquationRight1Rule]] or an [[EquationRight2Rule]] according to which replacement is sensible. 
   */
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val eq = eqocc.formula

    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val aux = auxocc.formula
        val term = aux.get(pos)

        term match {
          case Some(`s`) => EquationRight1Rule(s1, s2, term1oc, term2oc, pos)

          case Some(`t`) => EquationRight2Rule(s1, s2, term1oc, term2oc, pos)

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }
  
  
  /** This version of the rule operates on formulas instead of occurrences. It will attempt to find appropriate occurrences in the premises.
    *
    * @param s1 A proof ending with term1oc in the succedent.
    * @param s2 A proof ending with term2oc in the succedent.
    * @param term1 An equation s = t.
    * @param term2 A formula A.
    * @param main A formula A' such that A' is obtained by replacing one occurrence of s in A by t or vice versa.
    * @return A proof ending with either an [[EquationRight1Rule]] or an [[EquationRight2Rule]] according to which one leads from A to A'.
    */
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
    (s1.root.succedent.filter(x => x.formula == term1).toList, s2.root.succedent.filter(x => x.formula == term2).toList) match {
      case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    }

  private def getTerms(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    val term2op = s2.succedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    else {
      val eqocc = term1op.get
      val auxocc = term2op.get
      (eqocc, auxocc)
    }
  }
}

/** Macro rule that simulates several term replacements at once.
 *
 */
object EquationLeftBulkRule extends EquationRuleLogger {

  /** Allows replacements at several positions in the auxiliary formula.
   *
   * @param s1 A proof ending with term1oc in the succedent.
   * @param s2 A proof ending with term2oc in the antecedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param sPos List of positions of terms that should be replaced by s.
   * @param tPos List of positions of terms that should be replaced by t.
   * @return A new proof whose main formula is A with every p in sPos replaced by s and every p in tPos replaced by t.
   */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, sPos: List[HOLPosition], tPos: List[HOLPosition]):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas = {
    val (eqocc, auxocc) = (s1.root.succedent.find(_ == term1oc), s2.root.antecedent.find(_ == term2oc)) match {
      case (Some(e), Some(a)) => (e,a)
      case _ => throw new LKRuleCreationException("Auxiliary formulas not found.")
    }
    val (eq, aux) = (eqocc.formula, auxocc.formula)
    
    trace("EquationLeftBulkRule called with equation "+term1oc+", aux formula "+term2oc+", s positions "+sPos+" and t positions "+tPos)

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")
        
        // Filter out those positions where no terms need to be replaced.
        val (sPosActive, tPosActive) = (sPos filter { aux.get(_) match { case Some(`t`) => true; case _ => false }}, 
                                        tPos filter { aux.get(_) match { case Some(`s`) => true; case _ => false }})
        val n = sPosActive.length + tPosActive.length
        
        trace(""+n+" replacements to make.")

        n match {
          case 0 => throw new Exception("This should never happen.")
          case 1 =>
            EquationLeftRule(s1, s2, term1oc, term2oc, (sPosActive ++ tPosActive).head)
          case _ =>

            // Initialize the proof currently being worked on and its auxiliary formula.
            var currentProofR = s2
            var currentAux = term2oc

            // Save newly created equations in a list so we can later contract them.
            val equations = new ListBuffer[FormulaOccurrence]

            // Iterate over the s-positions
            for (p <- sPosActive) aux.get(p) match {
              case Some(`s`) => trace("s found at s-position " + p + ", nothing to do.")
              case Some(`t`) =>
                
                // Generate a new instance of s = t :- s = t and save the formula in the antecedent in the equations list.
                val currentProofL = Axiom(List(eq), List(eq))
                equations += currentProofL.root.antecedent.head
                val currentEq = currentProofL.root.succedent.head
                
                // Create a subproof that replaces the term at p.
                currentProofR = EquationLeftRule(currentProofL, currentProofR, currentEq, currentAux, p)
                
                // The new auxiliary formula is the principal formula of the previous step.
                currentAux = currentProofR.asInstanceOf[PrincipalFormulas].prin(0)
                
              case _ => throw new LKRuleCreationException("Position " + p + " in formula " + aux + " does not contain term " + s + " or " + t + ".")
            }

            // Iterate over the t-positions. For comments see the previous loop.
            for (p <- tPosActive) aux.get(p) match {
              case Some(`s`) =>
                
                val currentProofL = Axiom(List(eq), List(eq))
                equations += currentProofL.root.antecedent.head
                val currentEq = currentProofL.root.succedent.head
                
                currentProofR = EquationLeftRule(currentProofL, currentProofR, currentEq, currentAux, p)
                
                currentAux = currentProofR.asInstanceOf[PrincipalFormulas].prin(0)
                
              case Some(`t`) => trace("t found at t-position " + p + ", nothing to do.")
              case _ => throw new LKRuleCreationException("Position " + p + " in formula " + aux + " does not contain term " + s + " or " + t + ".")
            }

            trace(""+n+" replacements made.")
            
            // Find the descendants of the saved equations in the current end sequent.
            val equationDescendants = equations.toList map{ currentProofR.getDescendantInLowerSequent } map { _.get }
            
            // Contract the equations.
            currentProofR = ContractionLeftBulkRule(currentProofR, equationDescendants)
            
            // Finally, remove the remaining occurrence of s = t with a cut.
            CutRule(s1, currentProofR, eqocc, currentProofR.asInstanceOf[PrincipalFormulas].prin(0))
        }
      case _ => throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /** Allows replacements at several positions in the auxiliary formula.
   *
   * @param s1 A proof ending with term1oc in the succedent.
   * @param s2 A proof ending with term2oc in the antecedent.
   * @param term1oc An equation s = t.
   * @param term2oc A formula A.
   * @param main The proposed main formula.
   * @return A new proof with principal formula main. Equation rules will be used according to the replacements that need to be made.
   */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas = {
    val (eqocc, auxocc) = (s1.root.succedent.find(_ == term1oc), s2.root.antecedent.find(_ == term2oc)) match {
      case (Some(e), Some(a)) => (e,a)
      case _ => throw new LKRuleCreationException("Auxiliary formulas not found.")
    }
    val (eq, aux) = (eqocc.formula, auxocc.formula)

    trace("EquationLeftBulkRule called with equation "+term1oc+", aux formula "+term2oc+" and main formula "+main)

    eq match {
      case Equation(s, t) =>

        trace("Equation: " + s + " = " + t + ".")

        if (s == t && aux == main) {
          warn("Producing equation rule with trivial equation.")
          EquationLeft1Rule(s1, s2, term1oc, term2oc, main)
        }

        else if (s == t && aux != main) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          // Find all positions of s and t in aux.
          val (auxS, auxT) = (aux.find(s), aux.find(t))

          // Find all positions of s and t in main.
          val (mainS, mainT) = (main.find(s), main.find(t))

          // Find the positions where actual replacements will happen.
          val (tToS, sToT) = (mainS intersect auxT, mainT intersect auxS)

          // Call the previous apply method.
          apply(s1, s2, term1oc, term2oc, tToS, sToT)
        }

      case _ => throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }
}

/** Macro rule that simulates several term replacements at once.
*
*/
object EquationRightBulkRule extends EquationRuleLogger {

  /** Allows replacements at several positions in the auxiliary formula.
    *
    * @param s1 A proof ending with term1oc in the succedent.
    * @param s2 A proof ending with term2oc in the succedent.
    * @param term1oc An equation s = t.
    * @param term2oc A formula A.
    * @param sPos List of positions of terms that should be replaced by s.
    * @param tPos List of positions of terms that should be replaced by t.
    * @return A new proof whose main formula is A with every p in sPos replaced by s and every p in tPos replaced by t.
    */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, sPos: List[HOLPosition], tPos: List[HOLPosition]):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas = {
    // Detailed comments can be found in the corresponding apply method for EquationLeftBulkRule!
    val (eqocc, auxocc) = (s1.root.succedent.find(_ == term1oc), s2.root.succedent.find(_ == term2oc)) match {
      case (Some(e), Some(a)) => (e,a)
      case _ => throw new LKRuleCreationException("Auxiliary formulas not found.")
    }
    val (eq, aux) = (eqocc.formula, auxocc.formula)
    
    trace("EquationRightBulkRule called with equation "+term1oc+", aux formula "+term2oc+", s positions "+sPos+" and t positions "+tPos)

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")
        val (sPosActive, tPosActive) = (sPos filter { aux.get(_) match { case Some(`t`) => true; case _ => false }},
                                        tPos filter { aux.get(_) match { case Some(`s`) => true; case _ => false }})
        val n = sPosActive.length + tPosActive.length
        trace(""+n+" replacements to make.")

        n match {
          case 0 => throw new Exception("This should never happen.")
          case 1 =>
            EquationRightRule(s1, s2, term1oc, term2oc, (sPosActive ++ tPosActive).head)
          case _ =>

            var currentProofR = s2
            var currentAux = term2oc

            val equations = new ListBuffer[FormulaOccurrence]

            for(p <- sPosActive) aux.get(p) match {
              case Some(`s`) => trace("s found at s-position "+p+", nothing to do.")
              case Some(`t`) =>
                val currentProofL = Axiom(List(eq), List(eq))
                equations += currentProofL.root.antecedent.head
                val currentEq = currentProofL.root.succedent.head
                
                currentProofR = EquationRightRule(currentProofL, currentProofR, currentEq, currentAux, p)
                currentAux = currentProofR.asInstanceOf[PrincipalFormulas].prin(0)
                
              case _ => throw new LKRuleCreationException("Position "+p+" in formula "+aux+" does not contain term "+s+" or " +t+".")
            }

            for (p <- tPosActive) aux.get(p) match {
              case Some(`s`) =>
                val currentProofL = Axiom(List(eq), List(eq))
                equations += currentProofL.root.antecedent.head
                val currentEq = currentProofL.root.succedent.head
                
                currentProofR = EquationRightRule(currentProofL, currentProofR, currentEq, currentAux, p)
                currentAux = currentProofR.asInstanceOf[PrincipalFormulas].prin(0)
                
              case Some(`t`) => trace("t found at t-position "+p+", nothing to do.")
              case _ => throw new LKRuleCreationException("Position " + p + " in formula " + aux + " does not contain term " + s + " or " + t + ".")
            }

            trace(""+n+" replacements made.")


            val equationDescendants = equations.toList map { currentProofR.getDescendantInLowerSequent } map { _.get }
            currentProofR = ContractionLeftBulkRule(currentProofR, equationDescendants)
            
            CutRule(s1, currentProofR, eqocc, currentProofR.asInstanceOf[PrincipalFormulas].prin(0))
        }
      case _ => throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /** Allows replacements at several positions in the auxiliary formula.
    *
    * @param s1 A proof ending with term1oc in the succedent.
    * @param s2 A proof ending with term2oc in the succedent.
    * @param term1oc An equation s = t.
    * @param term2oc A formula A.
    * @param main The proposed main formula.
    * @return A new proof with principal formula main. Equation rules will be used according to the replacements that need to be made.
    */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas = {
    val (eqocc, auxocc) = (s1.root.succedent.find(_ == term1oc), s2.root.succedent.find(_ == term2oc)) match {
      case (Some(e), Some(a)) => (e,a)
      case _ => throw new LKRuleCreationException("Auxiliary formulas not found.")
    }
    val (eq, aux) = (eqocc.formula, auxocc.formula)

    trace("EquationRightBulkRule called with equation "+term1oc+", aux formula "+term2oc+" and main formula "+main)

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (s == t && aux == main) {
          warn("Producing equation rule with trivial equation.")
          EquationRight1Rule(s1, s2, term1oc, term2oc, main)
        }

        else if (s == t && aux != main) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }


        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {

          // Find all positions of s and t in aux.
          val (auxS, auxT) = (aux.find(s), aux.find(t))

          // Find all positions of s and t in main.
          val (mainS, mainT) = (main.find(s), main.find(t))

          // Find the positions where actual replacements will happen.
          val (tToS, sToT) = (mainS intersect auxT, mainT intersect auxS)

          // Call the previous apply method.
          apply(s1, s2, term1oc, term2oc, tToS, sToT)

        }
      case _ => throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }
}

/** This macro rule simulates a series of contractions.
  *
  */
object ContractionLeftBulkRule {

  /**
   *
   * @param s1 A proof.
   * @param occs A list of FormulaOccurrences in the antecedent of s1. Needs to contain at least 2 elements.
   * @return A proof ending with as many contraction rules as necessary to contract occs into a single occurrence.
   */
  def apply(s1: LKProof, occs: List[FormulaOccurrence]):
  UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = occs match {
    case Nil | _ :: Nil => throw new LKRuleCreationException("Can't perform contraction on fewer than 2 formula occurrences.")
    case occ1 :: occ2 :: rest =>
      rest match {
        case Nil => ContractionLeftRule(s1, occ1, occ2)
          
        case _ =>
            val subProof = ContractionLeftRule(s1, occ1, occ2)
            val occ = subProof.prin(0)
            val restNew = rest map { subProof.getDescendantInLowerSequent }
            if (restNew.forall(_.isDefined))
              ContractionLeftBulkRule(subProof, occ :: restNew.map(_.get))
            else
              throw new LKRuleCreationException("Formula not found in sequent "+s1.root)
      }
  }

  /** Contracts all occurrences of one formula in the antecedent. Use with care!
   *
   * @param s1 A proof.
   * @param form A formula.
   * @return If form exists more than once in the antecedent, all occurrences will be contracted. Otherwise s1 is returned.
   */
  def apply(s1: LKProof, form: HOLFormula): Tree[Sequent] with LKProof = {
    val list = s1.root.antecedent.filter(_.formula == form).toList

    list match {
      case Nil | _ :: Nil => s1
      case _ => apply(s1, list)
    }
  }
}

/** This macro rule simulates a series of contractions.
  *
  */
object ContractionRightBulkRule {

  /**
   *
   * @param s1 A proof.
   * @param occs A list of FormulaOccurrences in the succedent of s1. Needs to contain at least 2 elements.
   * @return A proof ending with as many contraction rules as necessary to contract occs into a single occurrence.
   */
  def apply(s1: LKProof, occs: List[FormulaOccurrence]):
  UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = occs match {
    case Nil | _ :: Nil => throw new LKRuleCreationException("Can't perform contraction on fewer than 2 formula occurrences.")
    case occ1 :: occ2 :: rest =>
      rest match {
        case Nil => ContractionRightRule(s1, occ1, occ2)
          
        case _ =>
            val subProof = ContractionRightRule(s1, occ1, occ2)
            val occ = subProof.prin(0)
          val restNew = rest map { o => subProof.getDescendantInLowerSequent(o) }
          if (restNew.forall(o => o.isDefined))
            ContractionRightBulkRule(subProof, occ :: restNew.map(_.get))
          else
            throw new LKRuleCreationException("Formula not found in sequent "+s1.root)
      }
  }

  /** Contracts all occurrences of one formula in the succedent. Use with care!
    *
    * @param s1 A proof.
    * @param form A formula.
    * @return If form exists more than once in the succedent, all occurrences will be contracted. Otherwise s1 is returned.
    */
  def apply(s1: LKProof, form: HOLFormula): Tree[Sequent] with LKProof  = {
    val list = s1.root.succedent.filter(_.formula == form).toList

    list match {
      case Nil | _ :: Nil => s1
      case _ => apply(s1, list)
    }
  }
}

/** This macro rule simulates a series of weakenings in the antecedent.
 *
 */
object WeakeningLeftBulkRule {

  /**
   *
   * @param s1 A Proof.
   * @param list A list of HOLFormulas. Cannot be empty.
   * @return A new proof whose antecedent contains new occurrences of the formulas in list.
   */
  def apply(s1: LKProof, list: List[HOLFormula]):
  UnaryTree[Sequent] with UnaryLKProof with PrincipalFormulas= list match {
    case Nil => throw new LKRuleCreationException("Cannot create weakening rule with no weakenings.")
    case x :: Nil => WeakeningLeftRule(s1, x)
    case x :: xs =>
      val subProof = WeakeningLeftBulkRule(s1, xs)
      WeakeningLeftRule(subProof, x)
  }
}

/** This macro rule simulates a series of weakenings in the succedent.
  *
  */
object WeakeningRightBulkRule {

  /**
   *
   * @param s1 A Proof.
   * @param list A list of HOLFormulas. Cannot be empty.
   * @return A new proof whose succedent contains new occurrences of the formulas in list.
   */
  def apply(s1: LKProof, list: List[HOLFormula]):
  UnaryTree[Sequent] with UnaryLKProof with PrincipalFormulas= list match {
    case Nil => throw new LKRuleCreationException("Cannot create weakening rule with no weakenings.")
    case x :: Nil => WeakeningRightRule(s1, x)
    case x :: xs =>
      val subProof = WeakeningRightBulkRule(s1, xs)
      WeakeningRightRule(subProof, x)
  }
}

/** This macro rule simulates a series of weakenings in both cedents.
 *
 */
object WeakeningBulkRule {

  /** Note that antList and sucList may not both be empty.
   *
   * @param s1 A proof.
   * @param antList A list of formulas.
   * @param sucList A list of formulas.
   * @return A new proof whose antecedent and succedent contain new occurrences of the formulas in antList and sucList, respectively.
   */
  def apply(s1: LKProof, antList: List[HOLFormula], sucList: List[HOLFormula]): UnaryTree[Sequent] with UnaryLKProof with PrincipalFormulas = (antList, sucList) match {
    case (Nil, Nil) => throw new LKRuleCreationException("Cannot create weakening rule with no weakenings.")
    case (x :: xs, Nil)  => WeakeningLeftBulkRule(s1, antList)
    case (Nil, y :: ys) => WeakeningRightBulkRule(s1, sucList)
    case (x :: xs, y :: ys) =>
      val subProof = WeakeningLeftBulkRule(s1, antList)
      WeakeningRightBulkRule(subProof, sucList)
  }

  /** Note that this is only well-defined if targetSequent contains the end sequent of s1.
   *
   * @param s1 A proof.
   * @param targetSequent A sequent of formulas (not occurrences!).
   * @return A proof whose end sequent is targetSequent.
   */
  def apply(s1: LKProof, targetSequent: FSequent): Tree[Sequent] with LKProof = {
    val currentAnt = s1.root.antecedent map {_.formula}
    val currentSuc = s1.root.antecedent map {_.formula}

    val targetAnt = targetSequent.antecedent
    val targetSuc = targetSequent.succedent

    val (tmp1, tmp2) = (currentAnt diff targetAnt, currentSuc diff targetSuc)

    if (tmp1.nonEmpty || tmp2.nonEmpty)
      throw new LKRuleCreationException("End sequent of s1 is not contained in "+targetSequent+".")

    val (antList, sucList) = (targetAnt diff currentAnt, targetSuc diff currentSuc)

    if(antList.isEmpty && sucList.isEmpty)
      s1
    else
      WeakeningBulkRule(s1, antList.toList, sucList.toList)
  }
}