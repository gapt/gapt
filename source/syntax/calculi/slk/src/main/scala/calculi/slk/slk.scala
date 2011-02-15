package at.logic.calculi.slk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.calculi.lk.base._
import at.logic.language.hol._
import at.logic.language.schema._
import at.logic.utils.ds.trees._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.typedLambdaCalculus.{App, Abs}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

case object AndEquivalenceRule3Type extends UnaryRuleTypeA

object AndEquivalenceRule3 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigAnd(v, f, ub, lb) if ub == lb => {
          require( betaNormalize( App(Abs(v, f), ub) ) == auxf.formula )
          val prinFormula = PointerFOFactoryInstance.createPrincipalFormulaOccurrence( main, auxf::Nil )
          def createSide( s : Set[FormulaOccurrence] ) =
            if ( s.contains( auxf ) )
              createContext(s - auxf) + prinFormula
            else
              createContext(s)
          new UnaryTree[SequentOccurrence]( new SequentOccurrence( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
            with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
              def rule = AndEquivalenceRule3Type
              def aux = (auxf::Nil)::Nil
              def prin = prinFormula::Nil
            }
      }
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule3 must have a BigAnd as head symbol.")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == AndEquivalenceRule3Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}
