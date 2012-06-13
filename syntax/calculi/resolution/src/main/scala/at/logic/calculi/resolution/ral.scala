/*
 * ral.scala
 *
 * In this file, the rules of the R_{al} calculus
 * are defined.
 */
package at.logic.calculi.resolution

import at.logic.language.lambda.types._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.acyclicGraphs._
import scala.collection.immutable.{Seq,HashSet}
import scala.collection.mutable.Map
import at.logic.language.lambda.substitutions._
import base._
import andrews.SubType
import at.logic.utils.labeling._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.language.hol.skolemSymbols.TypeSynonyms._
import at.logic.calculi.lksk.base._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.calculi.lk.base.{Sequent,createContext => lkCreateContext,AuxiliaryFormulas,PrincipalFormulas, SubstitutionTerm}
import at.logic.utils.traits.Occurrence
//import at.logic.calculi.lk.base.{FormulaNotExistsException,Sequent,Sequent}

package ral {
  // inferences
  case object AllTRalType extends UnaryRuleTypeA
  case object AllFRalType extends UnaryRuleTypeA
  case object ExTRalType extends UnaryRuleTypeA
  case object ExFRalType extends UnaryRuleTypeA

  case object CutRalType extends UnaryRuleTypeA


  object Definitions {
    // TODO: maybe move these two to LKsk?
    def createContext(seq: Seq[FormulaOccurrence]): Seq[LabelledFormulaOccurrence] = lkCreateContext( seq ).asInstanceOf[Seq[LabelledFormulaOccurrence]]

    def computeSkolemTerm( sk: SkolemSymbol, t: TA, label: Label ) =
      Function(sk, label.toList, t)
  }

  import Definitions._
import util.grammar.LabelledRHS

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
        val sub = term1.formula match { case All(sub, _) => sub }
        val prinFormula = new LabelledFormulaOccurrence(betaNormalize( App( sub, v ) ).asInstanceOf[HOLFormula], term1::Nil, term1.skolem_label + v )
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
        // TODO: improve second match in next line
        val (sub, t) = term1.formula match { case All(sub, t) => (sub, t match { case ( (t -> To()) -> To() ) => t } ) }
        val skt = computeSkolemTerm( sk, t, term1.skolem_label ) //TODO: cast!?
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( App( sub, skt ) ).asInstanceOf[HOLFormula], term1::Nil).asInstanceOf[LabelledFormulaOccurrence] //TODO: is the cast really correct?
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
        val sub = term1.formula match { case Ex(sub, _) => sub }
        val prinFormula = new LabelledFormulaOccurrence(betaNormalize( App( sub, v ) ).asInstanceOf[HOLFormula], term1::Nil, term1.skolem_label + v )
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
        // TODO: improve second match in next line
        val (sub, t) = term1.formula match { case Ex(sub, t) => (sub, t match { case ( (t -> To()) -> To() ) => t } ) }
        val skt = computeSkolemTerm( sk, t, term1.skolem_label ) //TODO: cast!?
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( App( sub, skt ) ).asInstanceOf[HOLFormula], term1::Nil).asInstanceOf[LabelledFormulaOccurrence] //TODO: is the cast really correct?
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
    def apply[V <: Sequent](p: ResolutionProof[V], sub: Substitution[HOLExpression]) =
      new UnaryAGraph[Sequent](Sequent(
          p.root.antecedent.map(x => LKskFOFactory.createContextFormulaOccurrenceWithSubst( betaNormalize( sub(x.formula) ).asInstanceOf[HOLFormula], x, x::Nil, sub)), //TODO: cast!?!
          p.root.succedent.map(x => LKskFOFactory.createContextFormulaOccurrenceWithSubst( betaNormalize( sub(x.formula) ).asInstanceOf[HOLFormula], x, x::Nil, sub))), //TODO: cast!?!
        p)
          with UnaryResolutionProof[V] with AppliedSubstitution[HOLExpression] {def rule = SubType; def substitution = sub}

    def unapply[V <: Sequent](proof: ResolutionProof[V] with AppliedSubstitution[HOLExpression]) = if (proof.rule == SubType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AppliedSubstitution[HOLExpression]]
        Some((pr.root, pr.uProof, pr.substitution))
    }
  }
}
