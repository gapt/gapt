/*
 * ral.scala
 *
 * In this file, the rules of the R_{al} calculus
 * are defined.
 */

package at.logic.calculi.resolution.ral

import at.logic.calculi.resolution._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.calculi.lksk._
import at.logic.calculi.lksk.TypeSynonyms._
import at.logic.calculi.lk.base.{Sequent, AuxiliaryFormulas, PrincipalFormulas, SubstitutionTerm}
import at.logic.language.hol._
import at.logic.language.hol.BetaReduction._
import at.logic.language.hol.skolemSymbols.TypeSynonyms.SkolemSymbol
import at.logic.language.lambda.types._
import at.logic.utils.ds.acyclicGraphs._
import at.logic.utils.labeling._
import at.logic.utils.traits.Occurrence
import util.grammar.LabelledRHS

// inferences
case object AllTRalType extends UnaryRuleTypeA
case object AllFRalType extends UnaryRuleTypeA
case object ExTRalType extends UnaryRuleTypeA
case object ExFRalType extends UnaryRuleTypeA
case object CutRalType extends UnaryRuleTypeA
case object SubType extends UnaryRuleTypeA

object Cut {
  def apply[V <: Sequent](s1: ResolutionProof[V], s2: ResolutionProof[V], term1ocs: List[Occurrence], term2ocs: List[Occurrence]) = {
    if ( !term1ocs.isEmpty && !term2ocs.isEmpty ) throw new ResolutionRuleCreationException( "Cut in R_{al} must have at least one auxiliary formula on every side")
    val term1ops = term1ocs.map( term1oc => s1.root.succedent.find(x => x == term1oc) )
    val term2ops = term2ocs.map( term2oc => s2.root.antecedent.find(x => x == term2oc) )
    if ( term1ops.exists( x => x == None ) || term2ops.exists( x => x == None ) ) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1s = term1ops.map( x => x.get )
      val term2s = term2ops.map( x => x.get )
      if ( term1s.exists( x => term2s.exists( y => x != y ) ) ) throw new ResolutionRuleCreationException("Formulas to be cut are not identical")
      else {
        new BinaryAGraph[Sequent](new LabelledSequent(
            createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent filterNot(term2s contains (_))),
            createContext(s1.root.succedent filterNot(term1s contains (_))) ++ createContext(s2.root.succedent))
          , s1, s2)
          with BinaryResolutionProof[V] with AuxiliaryFormulas {
              def rule = CutRalType
              def aux = (term1s)::(term2s)::Nil
          }
      }
    }
  }

  def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == CutRalType) {
      val r = proof.asInstanceOf[BinaryResolutionProof[V] with AuxiliaryFormulas]
      val (a1::a2::Nil) = r.aux
      Some((r.uProof1, r.uProof2, r.root, a1, a2))
    }
    else None
}

object ForallT {
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: LabelledFormulaOccurrence, v: HOLVar ) = {
    val term1op = s1.root.succedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get.asInstanceOf[LabelledFormulaOccurrence]
      val f = instantiate(term1.formula, v)
      val prinFormula = new LabelledFormulaOccurrence(betaNormalize( f ), term1::Nil, term1.skolem_label + v )
      new UnaryAGraph[Sequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
        with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = AllTRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = v
        }
    }
  }

  def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == AllTRalType) {
      val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a::Nil)::Nil) = pr.aux
      val (p::Nil) = pr.prin
      Some((pr.uProof, pr.root.asInstanceOf[LabelledSequent], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }
}

object ForallF {
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: LabelledFormulaOccurrence, sk: SkolemSymbol ) = {
    val term1op = s1.root.antecedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get.asInstanceOf[LabelledFormulaOccurrence]
      val t = term1.formula match { case AllVar(x,_) => x.exptype }
      val skt = computeSkolemTerm( sk, t, term1.skolem_label )
      val f = instantiate(term1.formula, skt)
      val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence] //TODO: is the cast really correct?
      new UnaryAGraph[Sequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
        with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = AllFRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = skt
        }
    }
  }

  def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == AllFRalType) {
      val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a::Nil)::Nil) = pr.aux
      val (p::Nil) = pr.prin
      Some((pr.uProof, pr.root.asInstanceOf[LabelledSequent], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }  
}

object ExistsF {
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: LabelledFormulaOccurrence, v: HOLVar ) = {
    val term1op = s1.root.antecedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get.asInstanceOf[LabelledFormulaOccurrence]
      val f = instantiate(term1.formula, v)
      val prinFormula = new LabelledFormulaOccurrence(betaNormalize( f ), term1::Nil, term1.skolem_label + v )
      new UnaryAGraph[Sequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
        with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = ExFRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = v
        }
    }
  }

  def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == ExFRalType) {
      val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a::Nil)::Nil) = pr.aux
      val (p::Nil) = pr.prin
      Some((pr.uProof, pr.root.asInstanceOf[LabelledSequent], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }
}

object ExistsT {
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: LabelledFormulaOccurrence, sk: SkolemSymbol ) = {
    val term1op = s1.root.succedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get.asInstanceOf[LabelledFormulaOccurrence]
      val t = term1.formula match { case ExVar(x,_) => x.exptype }
      val skt = computeSkolemTerm( sk, t, term1.skolem_label )
      val f = instantiate(term1.formula, skt)
      val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence] //TODO: is the cast really correct?
      new UnaryAGraph[Sequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
        with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = ExTRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = skt
        }
    }
  }

  def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == ExTRalType) {
      val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
      val ((a::Nil)::Nil) = pr.aux
      val (p::Nil) = pr.prin
      Some((pr.uProof, pr.root.asInstanceOf[LabelledSequent], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }  
}

object Sub {
  def apply[V <: Sequent](p: ResolutionProof[V], sub: Substitution) =
    new UnaryAGraph[Sequent](Sequent(
        p.root.antecedent.map(x => LKskFOFactory.createContextFormulaOccurrenceWithSubst( betaNormalize( sub(x.formula) ), x, x::Nil, sub)),
        p.root.succedent.map(x => LKskFOFactory.createContextFormulaOccurrenceWithSubst( betaNormalize( sub(x.formula) ), x, x::Nil, sub))),
      p)
        with UnaryResolutionProof[V] with AppliedSubstitution {def rule = SubType; def substitution = sub}

  def unapply[V <: Sequent](proof: ResolutionProof[V] with AppliedSubstitution) = if (proof.rule == SubType) {
      val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AppliedSubstitution]
      Some((pr.root, pr.uProof, pr.substitution))
  }
}

