/*
 * andrews.scala
 *
 * This is Andrews resolution calculus from his 1971 paper, with additional rules
 * for additional connectives.
 */
package at.logic.calculi.resolution

import at.logic.language.lambda.types._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.acyclicGraphs._
import scala.collection.immutable.Set
import scala.collection.mutable.Map
import at.logic.language.lambda.substitutions._
import at.logic.calculi.lk.base._
import base._
import at.logic.utils.labeling._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.language.hol.skolemSymbols.TypeSynonyms._
import at.logic.utils.traits.Occurrence

package andrews {
/*  
  case class LabeledSequent(antecedentLabeled: List[Tuple2[HOLFormula,Labeled[List[HOLExpression]]]], succedentLabeled: List[Tuple2[HOLFormula,Labeled[List[HOLExpression]]]])
      extends Sequent(antecedentLabeled.map(_._1), succedentLabeled.map(_._1)) {
    override def removeFormulasAtIndices(inds: List[Int]) = LabeledSequent(
        antecedentLabeled.zipWithIndex.filter(x => !inds.contains(x._2)).map(x => x._1),
        succedentLabeled.zipWithIndex.filter(x => !inds.contains(x._2 + antecedentLabeled.size)).map(x => x._1)
      )
    // the following methods return both the antecedent/succedent without the formula and the removed formula
    def getAntecedentPairAtIndex(index: Int) = (antecedentLabeled(index), antecedentLabeled.zipWithIndex.filterNot(x => x._2 == index).map(x => x._1))
    def getSuccedentPairAtIndex(index: Int) = (succedentLabeled(index), succedentLabeled.zipWithIndex.filterNot(x => x._2 == index).map(x => x._1))
  }
*/

/*
  trait AndrewsResolutionProof extends Proof[Sequent]
  trait NullaryAndrewsResolutionProof extends LeafAGraph[Sequent] with AndrewsResolutionProof
  trait UnaryAndrewsResolutionProof extends UnaryAGraph[Sequent] with AndrewsResolutionProof {
    override def uProof = t.asInstanceOf[AndrewsResolutionProof]
  }
  trait BinaryLKProof extends BinaryAGraph[Sequent] with AndrewsResolutionProof {
    override def uProof1 = t1.asInstanceOf[AndrewsResolutionProof]
    override def uProof2 = t2.asInstanceOf[AndrewsResolutionProof]
  }
*/

  object Definitions {
    def computeSkolemTerm( sk: SkolemSymbol, t: TA, sub: HOLExpression ) =
      Function(sk, sub.getFreeAndBoundVariables._1.asInstanceOf[Set[HOLVar]].toList, t) //TODO: cast!?
  }

  import Definitions._

  // inferences
  case object NotTType extends UnaryRuleTypeA
  case object NotFType extends UnaryRuleTypeA
  case object OrTType extends UnaryRuleTypeA
  case object OrFLType extends UnaryRuleTypeA
  case object OrFRType extends UnaryRuleTypeA
  case object AndFType extends UnaryRuleTypeA
  case object AndTLType extends UnaryRuleTypeA
  case object AndTRType extends UnaryRuleTypeA 
  case object ImplTType extends UnaryRuleTypeA
  case object ImplFLType extends UnaryRuleTypeA
  case object ImplFRType extends UnaryRuleTypeA
  case object AllTType extends UnaryRuleTypeA
  case object AllFType extends UnaryRuleTypeA
  case object ExTType extends UnaryRuleTypeA
  case object ExFType extends UnaryRuleTypeA
  case object SubType extends UnaryRuleTypeA
  case object CutType extends BinaryRuleTypeA

  object Cut {
    def apply[V <: Sequent](s1: ResolutionProof[V], s2: ResolutionProof[V], term1oc: Occurrence, term2oc: Occurrence) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      val term2op = s2.root.antecedent.find(x => x == term2oc)
      if (term1op == None || term2op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (term1.formula != term2.formula) throw new ResolutionRuleCreationException("Formulas to be cut are not identical")
        else {
          new BinaryAGraph[Sequent](Sequent(
              createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent.filterNot(_ == term2)),
              createContext(s1.root.succedent filterNot(_ == term1)) ++ createContext(s2.root.succedent))
            , s1, s2)
            with BinaryResolutionProof[V] with AuxiliaryFormulas {
                def rule = CutType
                def aux = (term1::Nil)::(term2::Nil)::Nil
            }
        }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == CutType) {
        val r = proof.asInstanceOf[BinaryResolutionProof[V] with AuxiliaryFormulas]
        val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
        Some((r.uProof1, r.uProof2, r.root, a1, a2))
      }
      else None
  }


  object NotT {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case Neg(x) => x }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent) :+ prinFormula, createContext(s1.root.succedent filterNot(_ == term1))), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = NotTType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == NotTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }
  }

  object NotF {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case Neg(x) => x }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)), createContext(s1.root.succedent) :+ prinFormula), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = NotFType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == NotFType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }
  }

  object OrT {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val (sub1, sub2) = term1.formula match { case Or(x, y) => (x, y) }
        val prin1 = term1.factory.createFormulaOccurrence(sub1, term1::Nil)
        val prin2 = term1.factory.createFormulaOccurrence(sub2, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prin1 :+ prin2), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = OrTType
            def aux = (term1::Nil)::Nil
            def prin = prin1::prin2::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == OrTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p1::p2::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p1, p2))
    }  
  }

  object OrFL {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case Or(x, y) => x }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = OrFLType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == OrFLType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }
  }

  object OrFR {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case Or(x, y) => y }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = OrFRType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == OrFRType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }  
  }

  object AndF {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val (sub1, sub2) = term1.formula match { case And(x, y) => (x, y) }
        val prin1 = term1.factory.createFormulaOccurrence(sub1, term1::Nil)
        val prin2 = term1.factory.createFormulaOccurrence(sub2, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prin1 :+ prin2, createContext(s1.root.succedent)), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = AndFType
            def aux = (term1::Nil)::Nil
            def prin = prin1::prin2::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == AndFType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p1::p2::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p1, p2))
    }  
  }

  object AndTL {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case And(x, y) => x }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = AndTLType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == AndTLType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }
  }

  object AndTR {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case And(x, y) => y }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = AndTRType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == AndTRType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }  
  }

  object ImplT {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val (sub1, sub2) = term1.formula match { case Imp(x, y) => (x, y) }
        val prin1 = term1.factory.createFormulaOccurrence(sub1, term1::Nil)
        val prin2 = term1.factory.createFormulaOccurrence(sub2, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent) :+ prin1, createContext(s1.root.succedent filterNot(_ == term1)) :+ prin2), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = ImplTType
            def aux = (term1::Nil)::Nil
            def prin = prin1::prin2::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == ImplTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p1::p2::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p1, p2))
    }  
  }

  object ImplFL {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case Imp(x, y) => x }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)), createContext(s1.root.succedent) :+ prinFormula), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = ImplFLType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == ImplFLType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }
  }

  object ImplFR {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case Imp(x, y) => y }
        val prinFormula = term1.factory.createFormulaOccurrence(sub, term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas {
            def rule = ImplFRType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == ImplFRType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p))
    }  
  }


  object ForallT {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence, v: HOLVar ) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case All(sub, _) => sub }
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( App( sub, v ) ).asInstanceOf[HOLFormula], term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = AllTType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = v
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == AllTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p, pr.subst))
    }
  }

  object ForallF {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence, sk: SkolemSymbol ) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        // TODO: improve second match in next line
        val (sub, t) = term1.formula match { case All(sub, t) => (sub, t match { case ( (t -> To()) -> To() ) => t } ) }
        //println( t )
        val skt = computeSkolemTerm( sk, t, sub.asInstanceOf[HOLExpression] ) //TODO: cast!?
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( App( sub, skt ) ).asInstanceOf[HOLFormula], term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = AllFType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = skt
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == AllFType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p, pr.subst))
    }  
  }

  object ExistsF {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence, v: HOLVar ) = {
      val term1op = s1.root.antecedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val sub = term1.formula match { case Ex(sub, _) => sub }
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( App( sub, v ) ).asInstanceOf[HOLFormula], term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = ExFType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = v
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == ExFType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p, pr.subst))
    }
  }

  object ExistsT {
    def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: Occurrence, sk: SkolemSymbol ) = {
      val term1op = s1.root.succedent.find(x => x == term1oc)
      if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        // TODO: improve second match in next line
        val (sub, t) = term1.formula match { case Ex(sub, t) => (sub, t match { case ( (t -> To()) -> To() ) => t } ) }
        val skt = computeSkolemTerm( sk, t, sub.asInstanceOf[HOLExpression] ) //TODO: cast!?
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( App( sub, skt ) ).asInstanceOf[HOLFormula], term1::Nil)
        new UnaryAGraph[Sequent](Sequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
            def rule = ExTType
            def aux = (term1::Nil)::Nil
            def prin = prinFormula::Nil
            def subst = skt
          }
      }
    }

    def unapply[V <: Sequent](proof: ResolutionProof[V]) = if (proof.rule == ExTType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
        val ((a::Nil)::Nil) = pr.aux
        val (p::Nil) = pr.prin
        Some((pr.uProof, pr.root, a, p, pr.subst))
    }  
  }

  object Sub {
    def apply[V <: Sequent](p: ResolutionProof[V], sub: Substitution[HOLExpression]) =
      new UnaryAGraph[Sequent](Sequent(
//        p.root.antecedent.map(x => x.factory.createContextFormulaOccurrence( betaNormalize( sub(x.formula) ).asInstanceOf[HOLFormula], x, x::Nil, p.root.antecedent filterNot(_ == x))), //TODO: cast!?!
//        p.root.succedent.map(x => x.factory.createContextFormulaOccurrence( betaNormalize( sub(x.formula) ).asInstanceOf[HOLFormula], x, x::Nil, p.root.succedent filterNot(_ == x)))), //TODO: cast!?!
        p.root.antecedent.map(x => x.factory.createFormulaOccurrence( betaNormalize( sub(x.formula) ).asInstanceOf[HOLFormula], x::Nil)),
        p.root.succedent.map(x => x.factory.createFormulaOccurrence( betaNormalize( sub(x.formula) ).asInstanceOf[HOLFormula], x::Nil))),
        p)
          with UnaryResolutionProof[V] with AppliedSubstitution[HOLExpression] {def rule = SubType; def substitution = sub}

    def unapply[V <: Sequent](proof: ResolutionProof[V] with AppliedSubstitution[HOLExpression]) = if (proof.rule == SubType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AppliedSubstitution[HOLExpression]]
        Some((pr.root, pr.uProof, pr.substitution))
    }
  }
}
