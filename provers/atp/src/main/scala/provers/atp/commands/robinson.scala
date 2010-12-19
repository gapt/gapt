package at.logic.provers.atp.commands

import at.logic.provers.atp.commands.base.DataCommand
import at.logic.provers.atp.commands.sequents.SetSequentsCommand
import at.logic.calculi.resolution.robinson.{InitialClause, ClauseOccurrence, Clause}
import at.logic.provers.atp.Definitions._
import at.logic.calculi.resolution.base.ResolutionProof
import at.logic.calculi.occurrences.PointerFOFactoryInstance
import at.logic.utils.ds.PublishingBuffer
import at.logic.calculi.resolution.robinson.{Resolution, Variant, Factor}
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.fol.{FOLExpression, Atom}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.substitutions.Substitution

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 13, 2010
 * Time: 1:00:51 PM
 * To change this template use File | Settings | File Templates.
 */

package robinson {

import _root_.at.logic.language.hol.Formula

// adds to the state the initial set of resolution proofs, made from the input clauses
  case class SetClausesCommand(override val clauses: Iterable[Clause]) extends SetSequentsCommand[ClauseOccurrence](clauses) {
    def apply(state: State, data: Any) = {
      val pb = new PublishingBuffer[ResolutionProof[ClauseOccurrence]]
      clauses.foreach(x => pb += InitialClause(x)(PointerFOFactoryInstance))
      List((state += new Tuple2("clauses", pb), data))
    }
  }

  // create variants to a pair of two clauses
  case object VariantsCommand extends DataCommand[ClauseOccurrence] {
    def apply(state: State, data: Any) = {
      val p = data.asInstanceOf[Tuple2[ResolutionProof[ClauseOccurrence],ResolutionProof[ClauseOccurrence]]]
      List((state, (Variant(p._1),Variant(p._2))))
    }
  }

  case class ResolveCommand(alg: UnificationAlgorithm[FOLExpression]) extends DataCommand[ClauseOccurrence] {
    def apply(state: State, data: Any) = {
      val p = data.asInstanceOf[Tuple2[Tuple2[ResolutionProof[ClauseOccurrence],ResolutionProof[ClauseOccurrence]],Tuple2[FormulaOccurrence,FormulaOccurrence]]]
      val mgus = alg.unify(p._2._1.formula.asInstanceOf[FOLExpression], p._2._2.formula.asInstanceOf[FOLExpression])
      require(mgus.size < 2) // as it is first order it must have at most one mgu
      mgus.map(x => (state, Resolution(p._1._1,p._1._2,p._2._1,p._2._2,x.asInstanceOf[Substitution[FOLExpression]])))
    }
  }

  case class FactorCommand(alg: UnificationAlgorithm[FOLExpression]) extends DataCommand[ClauseOccurrence] {
    def apply(state: State, data: Any) = {
      val res@ Resolution(cls, pr1, pr2, occ1, occ2, sub) = data.asInstanceOf[ResolutionProof[ClauseOccurrence]]
      val factors1 = computeFactors(alg, pr1.root.succedent, pr1.root.succedent.filterNot(_ == occ1).toList, occ1, Substitution[FOLExpression]()/*sub.asInstanceOf[Substitution[FOLExpression]]*/, Nil)
      val factors2 = computeFactors(alg, pr2.root.antecedent, pr2.root.antecedent.filterNot(_ == occ2).toList, occ2, Substitution[FOLExpression]()/*sub.asInstanceOf[Substitution[FOLExpression]]*/, Nil)
      (state, res) :: ((for {
          (ls1,sub1) <- (Nil,Substitution[FOLExpression]())::factors1
          (ls2,sub2) <- (Nil,Substitution[FOLExpression]())::factors2
          if !(ls1.isEmpty && ls2.isEmpty)
        } yield {
          // we need to get the new occurrences from factor to be used in Resolution
          val (pr11,occ11) = if (ls1.isEmpty) (pr1, occ1) else {
            val factor1 = Factor(pr1, occ1, ls1, sub1.asInstanceOf[Substitution[FOLExpression]])
            (factor1, factor1.root.getChildOf(occ1).get)
          }
          val (pr21,occ21) = if (ls2.isEmpty) (pr2, occ2) else {
            val factor2 = Factor(pr2, occ2, ls2, sub2.asInstanceOf[Substitution[FOLExpression]])
            (factor2, factor2.root.getChildOf(occ2).get)
          }
          ((pr11,pr21),(occ11,occ21))
          //Resolution(pr11, pr21, occ11, occ21, sub)
        }
      ).flatMap(x => new ResolveCommand(alg).apply(state,x)))
    }

    // computes factors, calling recursively to smaller sets
    // it is assumed in each call that the sub from the previous round is already applied to the formulas
    private def computeFactors(alg: UnificationAlgorithm[FOLExpression], lits: Set[FormulaOccurrence], indices: List[FormulaOccurrence], formOcc: FormulaOccurrence,
                               sub: Substitution[FOLExpression], usedOccurrences: List[FormulaOccurrence]): List[Tuple2[List[FormulaOccurrence], Substitution[FOLExpression]]] =
      indices match {
        case Nil => Nil
        case x::Nil =>
          val mgus = alg.unify(sub(x.formula.asInstanceOf[FOLExpression]), sub(formOcc.formula.asInstanceOf[FOLExpression]))
          mgus match {
            case Nil => Nil
            case List(sub2 : Substitution[_]) => {
              val subst : Substitution[FOLExpression] = (sub2 compose sub)
              List( (x::usedOccurrences, subst) )
            }
          }
        case x::ls => {
            val facts = computeFactors(alg, lits, ls, formOcc, sub, usedOccurrences)
            facts.foldLeft(Nil: List[Tuple2[List[FormulaOccurrence], Substitution[FOLExpression]]])((ls,a) => ls
                ++ computeFactors(alg, lits, x::Nil, formOcc, a._2, a._1)) ++ facts ++ computeFactors(alg, lits, x::Nil, formOcc, sub, usedOccurrences)
        }
      }
  }

  /*case class ParamodulationCommand(alg: UnificationAlgorithm[FOLExpression]) extends DataCommand[ClauseOccurrence] {
    def apply(state: State, data: Any) = {
      val (p1,p2) = data.asInstanceOf[Tuple2[ResolutionProof[ClauseOccurrence],ResolutionProof[ClauseOccurrence]]]
      val ls = (for {
          l1 <- p1.root.succedent
          l2 <- p2.root.antecedent ++ p2.root.succedent
          if (isEquality(l1.formula))
        } yield (l1.formula,l2)) ++
        (for {
          l1 <- p2.root.succedent
          l2 <- p1.root.antecedent ++ p1.root.succedent
          if (isEquality(l1.formula))
        } yield (l1.formula,l2))

    }
    def isEquality(f: Formula): Boolean = f.formula match {case Atom(ConstantStringSymbol("="), _::_::Nil) => true; _ => false}
  }  */
}