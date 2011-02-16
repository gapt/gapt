package at.logic.calculi.slk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.calculi.lk.base._
import at.logic.language.schema._
import at.logic.utils.ds.trees._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.typedLambdaCalculus.{App, Abs}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

import scala.collection.immutable.HashSet

case object AndEquivalenceRule1Type extends UnaryRuleTypeA
case object AndEquivalenceRule2Type extends UnaryRuleTypeA
case object AndEquivalenceRule3Type extends UnaryRuleTypeA
case object SchemaProofLinkRuleType extends NullaryRuleTypeA

trait SchemaProofLink {
  def link: String
  def indices: List[IntegerTerm]
}

object SchemaProofLinkRule {
  def apply(name: String, indices : List[IntegerTerm]) = {
    // TODO: should we compute the correct end-sequent here?
    new LeafTree[SequentOccurrence]( new SequentOccurrence( new HashSet, new HashSet ) ) with NullaryLKProof with SchemaProofLink {
      def rule = SchemaProofLinkRuleType
      def link = name
      def indices = indices
    }
  }

  def unapply( proof: LKProof ) = if (proof.rule == SchemaProofLinkRuleType) {
    val r = proof.asInstanceOf[NullaryLKProof with SchemaProofLink]
    Some(r.name, r.indices)
  }
  else None
}

object AndEquivalenceRule1 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigAnd(v, f, ub, Succ(lb)) => {
          require( And( BigAnd( v, f, ub, lb ), betaNormalize( App(Abs(v, f), Succ(lb)) ).asInstanceOf[SchemaFormula] ) == auxf.formula )
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
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule1 must have a BigAnd as head symbol.")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == AndEquivalenceRule1Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object AndEquivalenceRule2 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigAnd(v, f, ub, lb) => {
          require( And( BigAnd( v, f, Succ(ub), lb ), betaNormalize( App(Abs(v, f), ub) ).asInstanceOf[SchemaFormula] ) == auxf.formula )
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
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule2 must have a BigAnd as head symbol.")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == AndEquivalenceRule1Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

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
