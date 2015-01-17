/*
 * equationalRules.scala
 *
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.utils.ds.trees._
import base._
import at.logic.language.lambda.{ rename => renameLambda, freeVariables => freeVariablesLambda, Substitution => SubstitutionLambda, _}
import at.logic.utils.logging._
import org.slf4j.LoggerFactory

trait EquationRuleLogger extends Logger {
  override def loggerName = "EquationRuleLogger"
}

// Equational rules
case object EquationLeft1RuleType extends BinaryRuleTypeA
case object EquationLeft2RuleType extends BinaryRuleTypeA
case object EquationRight1RuleType extends BinaryRuleTypeA
case object EquationRight2RuleType extends BinaryRuleTypeA

case object UnaryEquationLeft1RuleType extends UnaryRuleTypeA
case object UnaryEquationLeft2RuleType extends UnaryRuleTypeA
case object UnaryEquationRight1RuleType extends UnaryRuleTypeA
case object UnaryEquationRight2RuleType extends UnaryRuleTypeA


  //TODO: perhaps there is a better place for this
  object EquationVerifier {
    //results
    abstract class ReplacementResult
    case object Equal extends ReplacementResult
    case object Different extends ReplacementResult
    case class EqualModuloEquality(path : List[Int]) extends ReplacementResult

    def apply(s : HOLExpression, t : HOLExpression, e1 : HOLExpression, e2 : HOLExpression) = checkReplacement(s,t,e1,e2)
    //this is a convenience method, apart from that everything is general
    def apply(eq : HOLFormula, e1 : HOLFormula, e2:HOLFormula) : Option[List[Int]] = {
      //println("try "+eq+" "+e1+" "+e2)
      eq match {
        case Equation(s,t) => apply(s,t,e1,e2) match {
          case EqualModuloEquality(path) =>
            //println("result:"+path)
            Some(path)
          case _ =>
            //println("no result")
            None
        }
        case _ => throw new Exception("Error checking for term replacement in "+e1+" and "+e2+": "+eq+" is not an equation!")
      }
    }

    def checkReplacement(s : LambdaExpression, t : LambdaExpression, e1 : LambdaExpression, e2 : LambdaExpression) : ReplacementResult = {
      //trace("matching "+e1+" against "+e2+" for "+s+" -> "+t)
      (e1,e2) match {
        case _ if e1 == e2 => Equal
        case _ if (e1 == s) && (e2 == t) => EqualModuloEquality(Nil)
        case (Var(_,_), Var(_,_)) => Different
        case (Const(_,_), Const(_,_)) => Different
        case (App(l1,r1), App(l2,r2)) =>
          (checkReplacement(s,t,l1,l2), checkReplacement(s,t,r1,r2)) match {
            case (Equal, Equal) => Equal
            case (EqualModuloEquality(path), Equal) => EqualModuloEquality(1::path)
            case (Equal, EqualModuloEquality(path)) => EqualModuloEquality(2::path)
            case _ => Different
          }
        case (Abs(v1@Var(name1,expt1),t1), Abs(v2@Var(name2,expt2),t2)) =>
          if (expt1 != expt2)
            Different
          else {
            val vn = renameLambda(v1, freeVariablesLambda(s) ++ freeVariablesLambda(t) ++ freeVariablesLambda(t1) ++ freeVariablesLambda(t2) ) //TODO: pass the list on instead of recreating it
            checkReplacement(s,t, SubstitutionLambda(v1,vn)(t1), SubstitutionLambda(v2,vn)(t2))
          }
        case _ => Different
      }
    }

  }

  // TODO: implement verification of the rule
  object EquationLeft1Rule extends EquationRuleLogger {
    /** <pre>Constructs a proof ending with a EqLeft rule.
      * In it, a formula A (marked by term2oc) is replaced by formula main.
      *
      * This method tests whether the proposed auxiliary and main formulas differ in exactly one place.
      * If so, it calls the next one with that position.
      * 
      * The rule: 
      * (rest of s1)       (rest of s2)
      * sL |- a=b, sR    tL, A[T1/a] |- tR
      * ------------------------------------ (EqLeft1)
      *      sL, A[T1/b], tL |- sR, tR
      * </pre>
      * 
      * @param s1 The left proof with the equation a=b in the succedent in its bottommost sequent.
      * @param s2 The right proof with a formula A[T1/a] in the antecedent of its bottommost sequent,
      *        in which some term T1 has been replaced by the term a. Note that identical terms to
      *        T1 may occur elsewhere in A. These will not be changed.
      *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
      *        This allows selective replacing of terms.
      * @param term1oc The occurrence (a=b) in s1.
      * @param term2oc The occurrence of A[T1/a] in s2.
      * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
      * @return An LK Proof ending with the new inference.
      */ 
    def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
      BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
      val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
      val aux = auxocc.formula
      val eq = eqocc.formula

      eq match {
        case Equation(s, t) =>
          trace("Equation: " +s+" = "+t+".")

          if (main == aux && s == t) {
            debug("aux and main formula are equal.")

            val sAux = aux.find(s)

            if (sAux.isEmpty)
              throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

            apply(s1, s2, term1oc, term2oc, sAux.head)
          }

          else if ((s == t) && (main != aux)) {
            throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
          }

          else if (s != t && aux == main) {
            throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
          }

          else {
            val sAux = aux.find(s)
            val tMain = main.find(t)

            if (sAux.isEmpty)
              throw new LKRuleCreationException("Term " + s + " not found in formula " + aux + ".")

            trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
            trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")
            val posList = sAux intersect tMain
            trace("posList = " + posList)

            if (posList.length == 1) {
              val p = posList.head
              val mainNew = HOLPosition.replace(aux, p, t)
              if (mainNew == main) {
                apply(s1, s2, term1oc, term2oc, p)
              }
              else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
            }
            else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
          }
        case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
      }
    }

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
            case Some(`s`) =>
              val prin = HOLPosition.replace(aux, pos, t).asInstanceOf[HOLFormula]
              val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
              val ant1 = createContext(s1.root.antecedent)
              val ant2 = createContext(s2.root.antecedent.filterNot(_ == auxocc))
              val antecedent = ant1 ++ ant2 :+ prinOcc
              val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
              val suc2 = createContext(s2.root.succedent)
              val succedent = suc1 ++ suc2

              new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2)
                with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
                def rule = EquationLeft1RuleType

                def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

                def prin = prinOcc :: Nil
                
                def termPos = List(pos)

                override def name = "e:l1"
              }

            case Some(x) =>
              throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

            case None =>
              throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
          }

        case _ =>
          throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
      }
    }


  /** <pre>Constructs a proof ending with a EqLeft rule.
    * In it, a formula A (marked by term2oc) is replaced by formula main.
    * This function merely returns the resulting sequent, not a proof.
    *
    * This rule does not check for the correct use of the =-symbol.
    * The burden of correct usage is on the programmer!
    * 
    * The rule: 
    *     (s1)               (s2)
    * sL |- a=b, sR    tr, A[T1/a] |- tR
    * ------------------------------------ (EqLeft1)
    *      sL, A[T1/b], tL |- sR, tR
    * </pre>
    * 
    * @param s1 The left sequent with the equarion a=b in its succent.
    * @param s2 The right sequent with a formula A[T1/a] in the antecedent of its bottommost sequent,
    *        in which some term T1 has been replaced by the term a. Note that identical terms to
    *        T1 may occur elsewhere in A. These will not be changed.
    *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
    *        This allows selective replacing of terms.
    * @param term1oc The occurrence (a=b) in s1.
    * @param term2oc The occurrence of A[T1/a] in s2.
    * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
    * @return The sequent (sL, A[T1/b], tL |- sR, tR).
    */ 
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (main == aux && s == t) {
          debug("aux and main formula are equal.")

          val sAux = aux.find(s)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

          apply(s1, s2, term1oc, term2oc, sAux.head)
        }

        else if (s == t && main != aux) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val sAux = aux.find(s)
          val tMain = main.find(t)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Term " + s + " not found in formula " + aux + ".")

          trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
          trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")
          val posList = sAux intersect tMain
          trace("posList = " + posList)

          if (posList.length == 1) {
            val p = posList.head
            val mainNew = HOLPosition.replace(aux, p, t)
            if (mainNew == main) {
              apply(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
        }
      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

    def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):Sequent = {
      val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
      val eq = eqocc.formula

      eq match {
        case Equation(s, t) =>
          trace("Equation: " +s+" = "+t+".")
          val aux = auxocc.formula
          val term = aux.get(pos)

          term match {
            case Some(`s`) =>
              val prin = HOLPosition.replace(aux, pos, t).asInstanceOf[HOLFormula]
              val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
              val ant1 = createContext(s1.antecedent)
              val ant2 = createContext(s2.antecedent.filterNot(_ == auxocc))
              val antecedent = ant1 ++ ant2 :+ prinOcc
              val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
              val suc2 = createContext(s2.succedent)
              val succedent = suc1 ++ suc2

              Sequent(antecedent, succedent)
            case Some(x) =>
              throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

            case None =>
              throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
          }

        case _ =>
          throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
      }
    }

  /** <pre>Constructs a proof ending with a EqLeft rule.
    * In it, a formula term2 of the form A[T1/a] is replaced by formula main.
    *
    * This rule does not check for the correct use of the =-symbol.
    * The burden of correct usage is on the programmer!
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr, A[T1/a] |- tR
    * ------------------------------------ (EqLeft1)
    *      sL, A[T1/b], tL |- sR, tR
    * </pre>
    * 
    * @param s1 The left proof with the equarion a=b in the succent in its bottommost sequent.
    * @param s2 The right proof with a formula A[T1/a] in the antecedent of its bottommost sequent,
    *        in which some term T1 has been replaced by the term a. Note that identical terms to
    *        T1 may occur elsewhere in A. These will not be changed.
    *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
    *        This allows selective replacing of terms.
    * @param term1 The formula (a=b) in s1.
    * @param term2 The formula A[T1/a] in s2.
    * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    (s1.root.succedent.filter(x => x.formula == term1).toList, s2.root.antecedent.filter(x => x.formula == term2).toList) match {
      case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
      case _ => throw new LKRuleCreationException("No matching formula occurrences found for application of the rule with the given formula")
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

  def unapply(proof: LKProof) = if (proof.rule == EquationLeft1RuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
}

// TODO: implement verification of the rule
object EquationLeft2Rule extends EquationRuleLogger {
  /** <pre>See EquationLeft1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
    *
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr, A[T1/b] |- tR
    * ------------------------------------ (EqLeft2)
    *      sL, A[T1/a], tL |- sR, tR
    * </pre>
    */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions= {
    //trace("s1: "+s1+", s2: "+s2+", term1oc: "+term1oc+", term2oc: "+term2oc+", main: "+main)
    val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (main == aux && s == t) {
          debug("aux and main formula are equal.")

          val sAux = aux.find(s)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

          apply(s1, s2, term1oc, term2oc, sAux.head)
        }

        else if (s == t && main != aux) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val tAux = aux.find(t)
          val sMain = main.find(s)

          if (tAux.isEmpty)
            throw new LKRuleCreationException("Term " + t + " not found in formula " + aux + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")
          val posList = tAux intersect sMain
          trace("posList = " + posList)

          if (posList.length == 1) {
            val p = posList.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              apply(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
        }

      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

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
          case Some(`t`) =>
            val prin = HOLPosition.replace(aux, pos, s).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val ant1 = createContext(s1.root.antecedent)
            val ant2 = createContext(s2.root.antecedent.filterNot(_ == auxocc))
            val antecedent = ant1 ++ ant2 :+ prinOcc
            val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
            val suc2 = createContext(s2.root.succedent)
            val succedent = suc1 ++ suc2

            new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2)
              with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
              def rule = EquationLeft2RuleType

              def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

              def prin = prinOcc :: Nil

              def termPos = List(pos)

              override def name = "e:l2"
            }

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /** <pre>See EquationLeft1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
    *
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr, A[T1/b] |- tR
    * ------------------------------------ (EqLeft2)
    *      sL, A[T1/a], tL |- sR, tR
    * </pre>
    */
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (main == aux && s == t) {
          debug("aux and main formula are equal.")

          val sAux = aux.find(s)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

          apply(s1, s2, term1oc, term2oc, sAux.head)
        }

        else if (s == t && main != aux) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val tAux = aux.find(t)
          val sMain = main.find(s)

          if (tAux.isEmpty)
            throw new LKRuleCreationException("Term " + t + " not found in formula " + aux + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")
          val posList = tAux intersect sMain
          trace("posList = " + posList)

          if (posList.length == 1) {
            val p = posList.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              apply(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
        }

      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")
        val aux = auxocc.formula
        val term = aux.get(pos)

        term match {
          case Some(`t`) =>
            val prin = HOLPosition.replace(aux, pos, s).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val ant1 = createContext(s1.antecedent)
            val ant2 = createContext(s2.antecedent.filterNot(_ == auxocc))
            val antecedent = ant1 ++ ant2 :+ prinOcc
            val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
            val suc2 = createContext(s2.succedent)
            val succedent = suc1 ++ suc2

            Sequent(antecedent, succedent)
          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /** <pre>See EquationLeft1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
    *
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr, A[T1/b] |- tR
    * ------------------------------------ (EqLeft2)
    *      sL, A[T1/a], tL |- sR, tR
    * </pre>
    */
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
    (s1.root.succedent.filter(x => x.formula == term1).toList, s2.root.antecedent.filter(x => x.formula == term2).toList) match {
    case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
    case _ => throw new LKRuleCreationException("No matching formula occurrences found for application of the rule with the given formula")
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

  def unapply(proof: LKProof) = if (proof.rule == EquationLeft2RuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
}

// TODO: implement verification of the rule
object EquationRight1Rule extends EquationRuleLogger {

  /** <pre>Constructs a proof ending with a EqRight rule.
    * In it, a formula A (marked by term2oc) is replaced by formula main.
    *
    * This rule does not check for the correct use of the =-symbol.
    * The burden of correct usage is on the programmer!
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr |- tR, A[T1/a]
    * ------------------------------------ (EqRight1)
    *      sL, tL |- sR, tR, A[T1/b]
    * </pre>
    * 
    * @param s1 The left proof with the equarion a=b in the succent in its bottommost sequent.
    * @param s2 The right proof with a formula A[T1/a] in the succedent of its bottommost sequent,
    *        in which some term T1 has been replaced by the term a. Note that identical terms to
    *        T1 may occur elsewhere in A. These will not be changed.
    *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
    *        This allows selective replacing of terms.
    * @param term1oc The occurrence (a=b) in s1.
    * @param term2oc The occurrence of A[T1/a] in s2.
    * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
    * @return An LK Proof ending with the new inference.
    */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    //trace("s1: "+s1+", s2: "+s2+", term1oc: "+term1oc+", term2oc: "+term2oc+", main: "+main)
    val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (main == aux && s == t) {
          debug("aux and main formula are equal.")

          val sAux = aux.find(s)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

          apply(s1, s2, term1oc, term2oc, sAux.head)
        }

        else if ((s == t) && (main != aux)) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val sAux = aux.find(s)
          val tMain = main.find(t)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Term " + s + " not found in formula " + aux + ".")

          trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
          trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")
          val posList = sAux intersect tMain
          trace("posList = " + posList)

          if (posList.length == 1) {
            val p = posList.head
            val mainNew = HOLPosition.replace(aux, p, t)
            if (mainNew == main) {
              apply(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
        }

      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

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
          case Some(`s`) =>
            val prin = HOLPosition.replace(aux, pos, t).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val ant1 = createContext(s1.root.antecedent)
            val ant2 = createContext(s2.root.antecedent)
            val antecedent = ant1 ++ ant2
            val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
            val suc2 = createContext(s2.root.succedent.filterNot(_ == auxocc))
            val succedent = suc1 ++ suc2 :+ prinOcc

            new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2)
              with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
              def rule = EquationRight1RuleType

              def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

              def prin = prinOcc :: Nil

              def termPos = List(pos)

              override def name = "e:r1"
            }

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }


  /** <pre>Constructs a proof ending with a EqLeft rule.
    * In it, a formula A (marked by term2oc) is replaced by formula main.
    * This function merely returns the resulting sequent, not a proof.
    *
    * This rule does not check for the correct use of the =-symbol.
    * The burden of correct usage is on the programmer!
    * 
    * The rule: 
    *    (s1)               (s2)
    * sL |- a=b, sR    tr |- tR, A[T1/a]
    * ------------------------------------ (EqRight1)
    *      sL, tL |- sR, tR, A[T1/b]
    * </pre>
    * 
    * @param s1 The left sequent with the equarion a=b in its succedent.
    * @param s2 The right sequent with a formula A[T1/a] in the antecedent of its bottommost sequent,
    *        in which some term T1 has been replaced by the term a. Note that identical terms to
    *        T1 may occur elsewhere in A. These will not be changed.
    *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
    *        This allows selective replacing of terms.
    * @param term1oc The occurrence (a=b) in s1.
    * @param term2oc The occurrence of A[T1/a] in s2.
    * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
    * @return The sequent (sL, A[T1/b], tL |- sR, tR).
    */
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (main == aux && s == t) {
          debug("aux and main formula are equal.")

          val sAux = aux.find(s)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

          apply(s1, s2, term1oc, term2oc, sAux.head)
        }

        else if ((s == t) && (main != aux)) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val sAux = aux.find(s)
          val tMain = main.find(t)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Term " + s + " not found in formula " + aux + ".")

          trace("Positions of s = " + s + " in aux = " + aux + ": " + sAux + ".")
          trace("Positions of t = " + t + " in main = " + main + ": " + tMain + ".")
          val posList = sAux intersect tMain
          trace("posList = " + posList)

          if (posList.length == 1) {
            val p = posList.head
            val mainNew = HOLPosition.replace(aux, p, t)
            if (mainNew == main) {
              apply(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
        }

      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")
        val aux = auxocc.formula
        val term = aux.get(pos)

        term match {
          case Some(`s`) =>
            val prin = HOLPosition.replace(aux, pos, t).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val ant1 = createContext(s1.antecedent)
            val ant2 = createContext(s2.antecedent)
            val antecedent = ant1 ++ ant2
            val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
            val suc2 = createContext(s2.succedent.filterNot(_ == auxocc))
            val succedent = suc1 ++ suc2 :+ prinOcc

            Sequent(antecedent, succedent)
          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /** <pre>Constructs a proof ending with a EqRight rule.
    * In it, a term2 of the form A[T1/a] is replaced by formula main.
    *
    * This rule does not check for the correct use of the =-symbol.
    * The burden of correct usage is on the programmer!
    * 
    * The rule: 
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr |- tR, A[T1/a]
    * ------------------------------------ (EqRight1)
    *      sL, tL |- sR, tR, A[T1/b]
    * </pre>
    * 
    * @param s1 The left proof with the equarion a=b in the succent in its bottommost sequent.
    * @param s2 The right proof with a formula A[T1/a] in the succedent of its bottommost sequent,
    *        in which some term T1 has been replaced by the term a. Note that identical terms to
    *        T1 may occur elsewhere in A. These will not be changed.
    *        e.g. P([f(0)]) v -P(f(0)), where f(0) occurs twice, but T1 only refers to the bracketed f(0).
    *        This allows selective replacing of terms.
    * @param term1 The formula (a=b) in s1.
    * @param term2 The formula A[T1/a] in s2.
    * @param main The formula A[T1/b], in which T1 has been replaced by b instead.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
    (s1.root.succedent.filter(x => x.formula == term1).toList, s2.root.succedent.filter(x => x.formula == term2).toList) match {
    case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
    case _ => throw new LKRuleCreationException("No matching formula occurrences found for application of the rule with the given formula")
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

  def unapply(proof: LKProof) = if (proof.rule == EquationRight1RuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
}

// TODO: implement verification of the rule
object EquationRight2Rule extends EquationRuleLogger {

  /** <pre>See EquationRight1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
    *
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr |- tR, A[T1/b]
    * ------------------------------------ (EqRight1)
    *      sL, tL |- sR, tR, A[T1/a]
    * </pre>
    */
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula):
  BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    //trace("s1: "+s1+", s2: "+s2+", term1oc: "+term1oc+", term2oc: "+term2oc+", main: "+main)
    val (eqocc, auxocc) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (main == aux && s == t) {
          debug("aux and main formula are equal.")

          val sAux = aux.find(s)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

          apply(s1, s2, term1oc, term2oc, sAux.head)
        }

        else if ((s == t) && (main != aux)) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val tAux = aux.find(t)
          val sMain = main.find(s)

          if (tAux.isEmpty)
            throw new LKRuleCreationException("Term " + t + " not found in formula " + aux + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")
          val posList = tAux intersect sMain
          trace("posList = " + posList)

          if (posList.length == 1) {
            val p = posList.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              apply(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
        }

      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

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
          case Some(`t`) =>
            val prin = HOLPosition.replace(aux, pos, s).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val ant1 = createContext(s1.root.antecedent)
            val ant2 = createContext(s2.root.antecedent)
            val antecedent = ant1 ++ ant2
            val suc1 = createContext(s1.root.succedent.filterNot(_ == eqocc))
            val suc2 = createContext(s2.root.succedent.filterNot(_ == auxocc))
            val succedent = suc1 ++ suc2 :+ prinOcc

            new BinaryTree[Sequent](Sequent(antecedent, succedent), s1, s2)
              with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
              def rule = EquationRight1RuleType

              def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

              def prin = prinOcc :: Nil

              def termPos = List(pos)

              override def name = "e:r2"
            }

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  /** <pre>See EquationRight1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
    *
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr |- tR, A[T1/b]
    * ------------------------------------ (EqRight1)
    *      sL, tL |- sR, tR, A[T1/a]
    * </pre>
    */
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, main: HOLFormula): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val aux = auxocc.formula
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")

        if (main == aux && s == t) {
          debug("aux and main formula are equal.")

          val sAux = aux.find(s)

          if (sAux.isEmpty)
            throw new LKRuleCreationException("Equation is trivial, but term "+s+" does not occur in "+aux+".")

          apply(s1, s2, term1oc, term2oc, sAux.head)
        }

        else if ((s == t) && (main != aux)) {
          throw new LKRuleCreationException("Equation is trivial, but aux formula " + aux + " and main formula " + main + "differ.")
        }

        else if (s != t && aux == main) {
          throw new LKRuleCreationException("Nontrivial equation, but aux and main formula are equal.")
        }

        else {
          val tAux = aux.find(t)
          val sMain = main.find(s)

          if (tAux.isEmpty)
            throw new LKRuleCreationException("Term " + t + " not found in formula " + aux + ".")

          trace("Positions of t = " + t + " in aux = " + aux + ": " + tAux + ".")
          trace("Positions of s = " + s + " in main = " + main + ": " + sMain + ".")
          val posList = tAux intersect sMain
          trace("posList = " + posList)

          if (posList.length == 1) {
            val p = posList.head
            val mainNew = HOLPosition.replace(aux, p, s)
            if (mainNew == main) {
              apply(s1, s2, term1oc, term2oc, p)
            }
            else throw new LKRuleCreationException("Replacement (" + aux + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + ".")
          }
          else throw new LKRuleCreationException("Position list " + posList + " is not valid.")
        }

      case _ => throw new LKRuleCreationException("Formula "+eq+" is not an equation.")
    }
  }

  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition): Sequent = {
    val (eqocc, auxocc) = getTerms(s1, s2, term1oc, term2oc)
    val eq = eqocc.formula

    eq match {
      case Equation(s, t) =>
        trace("Equation: " +s+" = "+t+".")
        val aux = auxocc.formula
        val term = aux.get(pos)

        term match {
          case Some(`t`) =>
            val prin = HOLPosition.replace(aux, pos, s).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val ant1 = createContext(s1.antecedent)
            val ant2 = createContext(s2.antecedent)
            val antecedent = ant1 ++ ant2
            val suc1 = createContext(s1.succedent.filterNot(_ == eqocc))
            val suc2 = createContext(s2.succedent.filterNot(_ == auxocc))
            val succedent = suc1 ++ suc2 :+ prinOcc

            Sequent(antecedent, succedent)
          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new Exception("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new Exception("Formula occurrence "+eqocc+" is not an equation.")
    }
  }


  /** <pre>See EquationRight1Rule. Performs the same as EquationLeft1Rule.apply, but a and b are switched in the rule:
    *
    * (rest of s1)       (rest of s2)
    * sL |- a=b, sR    tr |- tR, A[T1/b]
    * ------------------------------------ (EqRight1)
    *      sL, tL |- sR, tR, A[T1/a]
    * </pre>
    */
  def apply(s1: LKProof, s2: LKProof, term1: HOLFormula, term2: HOLFormula, main: HOLFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas =
    (s1.root.succedent.filter(x => x.formula == term1).toList, s2.root.succedent.filter(x => x.formula == term2).toList) match {
    case ((x::_),(y::_)) => apply(s1, s2, x, y, main)
    case _ => throw new LKRuleCreationException("No matching formula occurrences found for application of the rule with the given formula")
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

  def unapply(proof: LKProof) = if (proof.rule == EquationRight2RuleType) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof1, r.uProof2, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
}


/*

object UnaryEquationLeft1Rule extends EquationRuleLogger {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):
  UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val eqoccOpt: Option[FormulaOccurrence] = s1.root.antecedent.find(_ == term1oc)
    val auxoccOpt: Option[FormulaOccurrence] = s1.root.antecedent.find(_ == term2oc)
    
    val (eqocc: FormulaOccurrence, auxocc: FormulaOccurrence) = if (eqoccOpt == None)
      throw new LKRuleCreationException("Equation "+eqoccOpt+" is not contained in antecedent of "+s1.root+".")
    else if (auxoccOpt == None)
      throw new LKRuleCreationException("Auxiliary formula "+auxoccOpt+" is not contained in antecedent of "+s1.root+".")
    else
      (eqoccOpt.get, auxoccOpt.get)
    val (eq, aux) = (eqocc.formula, auxocc.formula)
    
    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val term = aux.get(pos)

        term match {
          case Some(`s`) =>
            val prin = HOLPosition.replace(aux, pos, t).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val antecedent = createContext(s1.root.antecedent filterNot (_ == auxocc)) :+ prinOcc
            val succedent = createContext(s1.root.succedent)

            new UnaryTree[Sequent](Sequent(antecedent, succedent), s1)
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
              def rule = UnaryEquationLeft1RuleType

              def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

              def prin = prinOcc :: Nil

              def termPos = List(pos)

              override def name = "e':l1"
            }

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  def unapply(proof: LKProof) = {
    if (proof.rule == UnaryEquationLeft1RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
  }
}

object UnaryEquationLeft2Rule extends EquationRuleLogger {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):
  UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val eqoccOpt = s1.root.antecedent.find(_ == term1oc)
    val auxoccOpt = s1.root.antecedent.find(_ == term2oc)

    val (eqocc: FormulaOccurrence, auxocc: FormulaOccurrence) = if (eqoccOpt == None)
      throw new LKRuleCreationException("Equation "+eqoccOpt+" is not contained in antecedent of "+s1.root+".")
    else if (auxoccOpt == None)
      throw new LKRuleCreationException("Auxiliary formula "+auxoccOpt+" is not contained in antecedent of "+s1.root+".")
    else
      (eqoccOpt.get, auxoccOpt.get)
    val (eq, aux) = (eqocc.formula, auxocc.formula)

    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val term = aux.get(pos)

        term match {
          case Some(`t`) =>
            val prin = HOLPosition.replace(aux, pos, s).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val antecedent = createContext(s1.root.antecedent filterNot (_ == auxocc)) :+ prinOcc
            val succedent = createContext(s1.root.succedent)

            new UnaryTree[Sequent](Sequent(antecedent, succedent), s1)
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
              def rule = UnaryEquationLeft2RuleType

              def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

              def prin = prinOcc :: Nil

              def termPos = List(pos)

              override def name = "e':l2"
            }

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  def unapply(proof: LKProof) = {
    if (proof.rule == UnaryEquationLeft2RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
  }
}

object UnaryEquationRight1Rule extends EquationRuleLogger {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):
  UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val eqoccOpt = s1.root.antecedent.find(_ == term1oc)
    val auxoccOpt = s1.root.succedent.find(_ == term2oc)

    val (eqocc: FormulaOccurrence, auxocc: FormulaOccurrence) = if (eqoccOpt == None)
      throw new LKRuleCreationException("Equation "+eqoccOpt+" is not contained in antecedent of "+s1.root+".")
    else if (auxoccOpt == None)
      throw new LKRuleCreationException("Auxiliary formula "+auxoccOpt+" is not contained in succedent of "+s1.root+".")
    else
      (eqoccOpt.get, auxoccOpt.get)
    val (eq, aux) = (eqocc.formula, auxocc.formula)

    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val term = aux.get(pos)

        term match {
          case Some(`s`) =>
            val prin = HOLPosition.replace(aux, pos, t).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val antecedent = createContext(s1.root.antecedent)
            val succedent = createContext(s1.root.succedent filterNot (_ == auxocc)) :+ prinOcc

            new UnaryTree[Sequent](Sequent(antecedent, succedent), s1)
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
              def rule = UnaryEquationRight1RuleType

              def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

              def prin = prinOcc :: Nil

              def termPos = List(pos)

              override def name = "e':r1"
            }

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }
  def unapply(proof: LKProof) = {
    if (proof.rule == UnaryEquationRight1RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
  }

}

object UnaryEquationRight2Rule extends EquationRuleLogger {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, pos: HOLPosition):
  UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions = {
    val eqoccOpt = s1.root.antecedent.find(_ == term1oc)
    val auxoccOpt = s1.root.succedent.find(_ == term2oc)

    val (eqocc: FormulaOccurrence, auxocc: FormulaOccurrence) = if (eqoccOpt == None)
      throw new LKRuleCreationException("Equation "+eqoccOpt+" is not contained in antecedent of "+s1.root+".")
    else if (auxoccOpt == None)
      throw new LKRuleCreationException("Auxiliary formula "+auxoccOpt+" is not contained in succedent of "+s1.root+".")
    else
      (eqoccOpt.get, auxoccOpt.get)
    val (eq, aux) = (eqocc.formula, auxocc.formula)

    eq match {
      case Equation(s,t) =>
        trace("Equation: " +s+" = "+t+".")
        val term = aux.get(pos)

        term match {
          case Some(`t`) =>
            val prin = HOLPosition.replace(aux, pos, s).asInstanceOf[HOLFormula]
            val prinOcc = eqocc.factory.createFormulaOccurrence(prin, List(eqocc, auxocc))
            val antecedent = createContext(s1.root.antecedent)
            val succedent = createContext(s1.root.succedent filterNot (_ == auxocc)) :+ prinOcc

            new UnaryTree[Sequent](Sequent(antecedent, succedent), s1)
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions {
              def rule = UnaryEquationRight2RuleType

              def aux = (eqocc :: Nil) :: (auxocc :: Nil) :: Nil

              def prin = prinOcc :: Nil

              def termPos = List(pos)

              override def name = "e':r2"
            }

          case Some(x) =>
            throw new LKRuleCreationException("Wrong term "+x+" in auxiliary formula "+aux+" at position "+pos+".")

          case None =>
            throw new LKRuleCreationException("Position "+pos+" is not well-defined for formula "+aux+".")
        }

      case _ =>
        throw new LKRuleCreationException("Formula occurrence "+eqocc+" is not an equation.")
    }
  }

  def unapply(proof: LKProof) = {
    if (proof.rule == UnaryEquationRight2RuleType) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with TermPositions]
      val ((eqocc::Nil)::(auxocc::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, eqocc, auxocc, r.termPos, p1))
    }
    else None
  }
}
*/

/*

object EquationRuleConverter {

  def toUnary(proof: LKProof): LKProof = applyRecursive(toUnaryHelper)(proof)

  def toBinary(proof:LKProof): LKProof = applyRecursive(toBinaryHelper)(proof)

  def toUnaryHelper(p: LKProof): LKProof = p match {
    case EquationLeft1Rule(u1, u2, _, term1oc, term2oc, posList, _) =>
      val subProof1 = WeakeningLeftRule(u2, term1oc.formula)
      val subProof2 = UnaryEquationLeft1Rule(subProof1, subProof1.prin(0), term2oc, posList(0))
      CutRule(u1, subProof2, term1oc, subProof2.aux(0)(0))

    case EquationLeft2Rule(u1, u2, _, term1oc, term2oc, posList, _) =>
      val subProof1 = WeakeningLeftRule(u2, term1oc.formula)
      val subProof2 = UnaryEquationLeft2Rule(subProof1, subProof1.prin(0), term2oc, posList(0))
      CutRule(u1, subProof2, term1oc, subProof2.aux(0)(0))

    case EquationRight1Rule(u1, u2, _, term1oc, term2oc, posList, _) =>
      val subProof1 = WeakeningLeftRule(u2, term1oc.formula)
      val subProof2 = UnaryEquationRight1Rule(subProof1, subProof1.prin(0), term2oc, posList(0))
      CutRule(u1, subProof2, term1oc, subProof2.aux(0)(0))

    case EquationRight2Rule(u1, u2, _, term1oc, term2oc, posList, _) =>
      val subProof1 = WeakeningLeftRule(u2, term1oc.formula)
      val subProof2 = UnaryEquationRight2Rule(subProof1, subProof1.prin(0), term2oc, posList(0))
      CutRule(u1, subProof2, term1oc, subProof2.aux(0)(0))

    case _ => p
  }

  def toBinaryHelper(p: LKProof): LKProof = p match {
    case UnaryEquationLeft1Rule(u1,_, term1oc, term2oc, posList,_) =>
      val eq = term1oc.formula
      val ax = Axiom(List(eq), List(eq))
      ContractionLeftRule(EquationLeft1Rule(ax, u1, ax.root.succedent(0), term2oc, posList(0)), eq)

    case UnaryEquationLeft2Rule(u1,_, term1oc, term2oc, posList,_) =>
      val eq = term1oc.formula
      val ax = Axiom(List(eq), List(eq))
      ContractionLeftRule(EquationLeft2Rule(ax, u1, ax.root.succedent(0), term2oc, posList(0)), eq)

    case UnaryEquationRight1Rule(u1,_, term1oc, term2oc, posList,_) =>
      val eq = term1oc.formula
      val ax = Axiom(List(eq), List(eq))
      ContractionLeftRule(EquationRight1Rule(ax, u1, ax.root.succedent(0), term2oc, posList(0)), eq)

    case UnaryEquationRight2Rule(u1,_, term1oc, term2oc, posList,_) =>
      val eq = term1oc.formula
      val ax = Axiom(List(eq), List(eq))
      ContractionLeftRule(EquationRight2Rule(ax, u1, ax.root.succedent(0), term2oc, posList(0)), eq)

    case _ => p
  }

}
*/
