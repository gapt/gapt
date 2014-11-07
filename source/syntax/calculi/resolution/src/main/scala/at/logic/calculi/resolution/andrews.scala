/*
 * andrews.scala
 *
 * This is Andrews resolution calculus from his 1971 paper, with additional rules
 * for additional connectives.
 */

package at.logic.calculi.resolution.andrews

import at.logic.calculi.resolution._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.hol.BetaReduction._
import at.logic.language.hol.skolemSymbols.TypeSynonyms.SkolemSymbol
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.utils.ds.acyclicGraphs._
import at.logic.calculi.lk.base.{Sequent, AuxiliaryFormulas, PrincipalFormulas, SubstitutionTerm}

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
  def apply[V <: Sequent](s1: ResolutionProof[V], s2: ResolutionProof[V], term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence) = {
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence, v: HOLVar ) = {
    val term1op = s1.root.succedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      val f = instantiate(term1.formula, v)
      val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil)
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence, sk: SkolemSymbol ) = {
    val term1op = s1.root.antecedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      // TODO: there must be a better way for getting this
      val (t, sub) = term1.formula match { case AllVar(v, sub) => ( v.exptype match { case ( (t -> To) -> To ) => t }, sub) }
      val skt = computeSkolemTerm( sk, t, sub )
      val f = instantiate(term1.formula, skt)
      val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil)
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence, v: HOLVar ) = {
    val term1op = s1.root.antecedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      val f = instantiate(term1.formula, v)
      val prinFormula = term1.factory.createFormulaOccurrence(betaNormalize(f), term1::Nil)
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
  def apply[V <: Sequent](s1: ResolutionProof[V], term1oc: FormulaOccurrence, sk: SkolemSymbol ) = {
    val term1op = s1.root.succedent.find(x => x == term1oc)
    if (term1op == None) throw new ResolutionRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      // TODO: there must be a better way for getting this
      val (t, sub) = term1.formula match { case ExVar(v, sub) => (v.exptype match { case ( (t -> To) -> To ) => t }, sub) }
      val skt = computeSkolemTerm( sk, t, sub )
      val f = instantiate(term1.formula, skt)
      val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil)
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
  def apply[V <: Sequent](p: ResolutionProof[V], sub: Substitution) =
    new UnaryAGraph[Sequent](Sequent(
      p.root.antecedent.map(x => x.factory.createFormulaOccurrence( betaNormalize( sub(x.formula) ), x::Nil)),
      p.root.succedent.map(x => x.factory.createFormulaOccurrence( betaNormalize( sub(x.formula) ), x::Nil))),
      p)
        with UnaryResolutionProof[V] with AppliedSubstitution {def rule = SubType; def substitution = sub}

  def unapply[V <: Sequent](proof: ResolutionProof[V] with AppliedSubstitution) = if (proof.rule == SubType) {
      val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AppliedSubstitution]
      Some((pr.root, pr.uProof, pr.substitution))
  }
}
