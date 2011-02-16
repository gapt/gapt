package at.logic.calculi.slk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.calculi.lk.base._
import at.logic.language.schema._
import at.logic.utils.ds.trees._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.typedLambdaCalculus.{App, Abs}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

case object AndEquivalenceRule1Type extends UnaryRuleTypeA
case object AndEquivalenceRule2Type extends UnaryRuleTypeA
case object AndEquivalenceRule3Type extends UnaryRuleTypeA
case object SchemaProofLinkRuleType extends NullaryRuleTypeA

// The following two classes are used to keep a global directory
// of proof schemata. Their definition is somewhat ad-hoc.

class SchemaProof(val name: String, val vars: List[IntVar], val base: LKProof, val rec: LKProof)

object SchemaProofDB {
  val proofs = new scala.collection.mutable.HashMap[String, SchemaProof]

  def get(name: String) = proofs(name)
  def put(proof: SchemaProof) = proofs.put(proof.name, proof)
}

trait SchemaProofLink {
  def link: String
  def indices: List[IntegerTerm]
}

object SchemaProofLinkRule {
  def apply(seq: Sequent, name: String, indices : List[IntegerTerm])(implicit factory: FOFactory) = {
    def createSide(side : List[SchemaFormula]) = side.foldLeft(Set.empty[FormulaOccurrence])((st, form) => st + factory.createPrincipalFormulaOccurrence(form, Nil, st))
    new LeafTree[SequentOccurrence]( SequentOccurrence(createSide(seq.antecedent.asInstanceOf[List[SchemaFormula]]), createSide(seq.succedent.asInstanceOf[List[SchemaFormula]]) ) ) with NullaryLKProof with SchemaProofLink {
      def rule = SchemaProofLinkRuleType
      def link = name
      def indices = indices
    }
  }

  def unapply( proof: LKProof ) = if (proof.rule == SchemaProofLinkRuleType) {
    val r = proof.asInstanceOf[NullaryLKProof with SchemaProofLink]
    Some(r.root, r.name, r.indices)
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

 // convenient extractors
  object UnarySchemaProof {
    def unapply(proof: LKProof) = proof match {
      case AndEquivalenceRule1(up, r, a, p) => Some((AndEquivalenceRule1Type, up, r, a::Nil, p))
      case AndEquivalenceRule2(up, r, a, p) => Some((AndEquivalenceRule2Type, up, r, a::Nil, p))
      case AndEquivalenceRule3(up, r, a, p) => Some((AndEquivalenceRule3Type, up, r, a::Nil, p))
      case _ => None
    }
  }