/*
 * ral.scala
 *
 * In this file, the rules of the R_{al} calculus
 * are defined.
 */

package at.logic.calculi.resolution.ral

import at.logic.calculi.lk.EquationVerifier
import at.logic.calculi.lk.EquationVerifier.{Different, EqualModuloEquality}
import at.logic.calculi.resolution._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.calculi.lksk._
import at.logic.calculi.lksk.TypeSynonyms._
import at.logic.calculi.lk.base._
import at.logic.calculi.resolution.createContext
import at.logic.language.hol._
import at.logic.language.hol.BetaReduction._
import at.logic.language.hol.skolemSymbols.TypeSynonyms.SkolemSymbol
import at.logic.language.lambda.types._
import at.logic.utils.ds.acyclicGraphs._
import at.logic.utils.ds.trees.LeafTree
import at.logic.utils.labeling._
//import util.grammar.LabelledRHS

// inferences
case object InitialRalType extends NullaryRuleTypeA
case object AllTRalType extends UnaryRuleTypeA
case object AllFRalType extends UnaryRuleTypeA
case object ExTRalType extends UnaryRuleTypeA
case object ExFRalType extends UnaryRuleTypeA
case object CutRalType extends BinaryRuleTypeA
case object ParaTRalType extends BinaryRuleTypeA
case object ParaFRalType extends BinaryRuleTypeA
case object SubType extends UnaryRuleTypeA
case object NegTRalType extends UnaryRuleTypeA
case object NegFRalType extends UnaryRuleTypeA
case object AndT1RalType extends UnaryRuleTypeA
case object AndT2RalType extends UnaryRuleTypeA
case object AndFRalType extends UnaryRuleTypeA
case object OrTRalType extends UnaryRuleTypeA
case object OrF1RalType extends UnaryRuleTypeA
case object OrF2RalType extends UnaryRuleTypeA
case object ImpTRalType extends UnaryRuleTypeA
case object ImpF1RalType extends UnaryRuleTypeA
case object ImpF2RalType extends UnaryRuleTypeA
case object AFactorTType extends UnaryRuleTypeA
case object AFactorFType extends UnaryRuleTypeA


trait Flip {
  /** *
    * in a paranmodulation rule with equation s=t, designate if it is used non-flipped (false) i.e. s=t or flipped (true) as t=s
    */
  val flipped : Boolean
}


trait RalResolutionProof[V <: LabelledSequent] extends ResolutionProof[V]
/* ********************* Cut and Quantifier Rules ****************************** */
object InitialSequent {
  def apply(seq: FSequent, maps: (List[Label], List[Label]))
  : RalResolutionProof[LabelledSequent] =
    createDefault(seq, maps, (x,y) => new LabelledSequent(x,y))._1


  def createDefault[V <: LabelledSequent](seq: FSequent, maps: (List[Label], List[Label]), sequent_constructor : (Seq[LabelledFormulaOccurrence], Seq[LabelledFormulaOccurrence]) => V): (RalResolutionProof[V], (List[LabelledFormulaOccurrence],List[LabelledFormulaOccurrence])) = {
    val left: Seq[LabelledFormulaOccurrence] =
      seq.antecedent.zip(maps._1).map( p => createOccurrence( p._1 , p._2 ) )
    val right: Seq[LabelledFormulaOccurrence] =
      seq.succedent.zip(maps._2).map( p => createOccurrence( p._1, p._2 ) )

    (new LeafTree[V](sequent_constructor(left, right ) )
      with RalResolutionProof[V] with NullaryResolutionProof[V] {
        def rule = InitialRalType
      },
      (left.toList,right.toList)
    )
  }

  def createOccurrence(f: HOLFormula, l: Label): LabelledFormulaOccurrence =
    LKskFOFactory.createInitialOccurrence(f, l)

  def unapply(proof: RalResolutionProof[LabelledSequent]) = if (proof.rule == InitialRalType) Some((proof.root)) else None
}

object Cut {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], s2: RalResolutionProof[V], term1ocs: List[FormulaOccurrence], term2ocs: List[FormulaOccurrence]) = {
    if ( term1ocs.isEmpty || term2ocs.isEmpty ) throw new ResolutionRuleCreationException( "Cut in R_{al} must have at least one auxiliary formula on every side")
    val term1ops = term1ocs.map( term1oc => s1.root.succedent.find(x => x == term1oc) )
    val term2ops = term2ocs.map( term2oc => s2.root.antecedent.find(x => x == term2oc) )
    if ( term1ops.exists( x => x == None ) || term2ops.exists( x => x == None ) ) throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    else {
      val term1s = term1ops.map( x => x.get )
      val term2s = term2ops.map( x => x.get )
      if ( term1s.exists( x => term2s.exists( y => x.formula != y.formula ) ) ) throw new ResolutionRuleCreationException("Formulas to be cut are not identical")
      else {
        new BinaryAGraph[LabelledSequent](new LabelledSequent(
          createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent filterNot(term2s contains (_))),
          createContext(s1.root.succedent filterNot(term1s contains (_))) ++ createContext(s2.root.succedent))
          , s1, s2)
          with RalResolutionProof[V] with BinaryResolutionProof[V] with AuxiliaryFormulas {
          def rule = CutRalType
          def aux = (term1s)::(term2s)::Nil
          override def name = "Cut"
        }
      }
    }
  }

  def unapply[V <: LabelledSequent](proof: RalResolutionProof[V]) = if (proof.rule == CutRalType) {
    val r = proof.asInstanceOf[BinaryResolutionProof[V] with AuxiliaryFormulas]
    val (a1::a2::Nil) = r.aux
    Some((r.root, r.uProof1.asInstanceOf[RalResolutionProof[V]], r.uProof2.asInstanceOf[RalResolutionProof[V]], a1, a2))
  }
  else None
}

object ForallT {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, v: HOLVar ) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val f = instantiate(term1.formula, v)
        val prinFormula = new LabelledFormulaOccurrence(betaNormalize( f ), term1::Nil, term1.skolem_label + v )
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = AllTRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = v
          override def name = "\u2200 T"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == AllTRalType) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }
  else None
}

object ForallF {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, sk: SkolemSymbol ) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val t = term1.formula match { case AllVar(x,_) => x.exptype }
        val skt = computeSkolemTerm( sk, t, term1.skolem_label )
        val f = instantiate(term1.formula, skt)
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = AllFRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = skt
          override def name = "\u2200 F"
        }

    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == AllFRalType) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }
  else None
}

object ExistsF {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, v: HOLVar ) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val f = instantiate(term1.formula, v)
        val prinFormula = new LabelledFormulaOccurrence(betaNormalize( f ), term1::Nil, term1.skolem_label + v )
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = ExFRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = v
          override def name = "\u2203 F"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == ExFRalType) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }
  else None
}

object ExistsT {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, sk: SkolemSymbol ) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val t = term1.formula match { case ExVar(x,_) => x.exptype }
        val skt = computeSkolemTerm( sk, t, term1.skolem_label )
        val f = instantiate(term1.formula, skt)
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
          def rule = ExTRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          def subst = skt
          override def name = "\u2203 T"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == ExTRalType) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence], pr.subst))
  }
  else None
}

object Sub {
  def apply[V <: LabelledSequent](p: RalResolutionProof[V], sub: Substitution) =
    new UnaryAGraph[LabelledSequent](new LabelledSequent(
      p.root.antecedent.map(x => LKskFOFactory.createContextFormulaOccurrenceWithSubst( x.formula, x, x::Nil, sub)),
      p.root.succedent.map(x => LKskFOFactory.createContextFormulaOccurrenceWithSubst( x.formula, x, x::Nil, sub))),
      p)
      with RalResolutionProof[V] with UnaryResolutionProof[V] with AppliedSubstitution {
      def rule = SubType;
      def substitution = sub
      override def name = "Sub"
    }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V] with AppliedSubstitution) = if (proof.rule == SubType) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AppliedSubstitution]
    Some((pr.root, pr.uProof.asInstanceOf[RalResolutionProof[V]], pr.substitution))
  }
  else None
}


/* ********************* Logical Rules ****************************** */
object NegF {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Neg(f) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)), createContext(s1.root.succedent) :+ prinFormula ), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = NegFRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u00ac F"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == NegFRalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object NegT {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Neg(f) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent) :+ prinFormula, createContext(s1.root.succedent filterNot(_ == term1))), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = NegTRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u00ac T"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == NegTRalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}


object AndT1 {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val And(l, _) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( l ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = AndT1RalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2227 T1"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == AndT1RalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object AndT2 {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val And(_, r) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( r ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = AndT1RalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2227 T2"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == AndT1RalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object OrF1 {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Or(l, _) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( l ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = OrF1RalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2228 F1"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == OrF1RalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object OrF2 {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Or(_, r) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( r ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = OrF2RalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2228 F2"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == OrF2RalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object ImpF1 {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Imp(l, _) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( l ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) :+ prinFormula, createContext(s1.root.succedent)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = ImpF1RalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
          override def name = "\u2283 F"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == ImpF1RalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object ImpF2 {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Imp(_, r) = term1.formula
        val prinFormula = term1.factory.createFormulaOccurrence( betaNormalize( r ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = ImpF2RalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula::Nil
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == ImpF2RalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object AndF {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val And(l, r) = term1.formula
        val prinFormula1 = term1.factory.createFormulaOccurrence( betaNormalize( l ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        val prinFormula2 = term1.factory.createFormulaOccurrence( betaNormalize( r ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(_ == term1)) ++ List(prinFormula1, prinFormula2), createContext(s1.root.succedent)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = AndFRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula1::prinFormula2::Nil
          override def name = "\u2227 F"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == AndFRalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p1::p2::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p1.asInstanceOf[LabelledFormulaOccurrence]), p2.asInstanceOf[LabelledFormulaOccurrence])
  }
  else None
}

object OrT {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Or(l, r) = term1.formula
        val prinFormula1 = term1.factory.createFormulaOccurrence( betaNormalize( l ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        val prinFormula2 = term1.factory.createFormulaOccurrence( betaNormalize( r ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(_ == term1)) ++ List(prinFormula1, prinFormula2)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = OrTRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula1::prinFormula2::Nil
          override def name = "\u2228 T"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == OrTRalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p1::p2::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p1.asInstanceOf[LabelledFormulaOccurrence]), p2.asInstanceOf[LabelledFormulaOccurrence])
  }
  else None
}

object ImpT {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
      case Some(term1) =>
        val Or(l, r) = term1.formula
        val prinFormula1 = term1.factory.createFormulaOccurrence( betaNormalize( l ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        val prinFormula2 = term1.factory.createFormulaOccurrence( betaNormalize( r ), term1::Nil).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(
          createContext(s1.root.antecedent) :+ prinFormula1,
          createContext(s1.root.succedent filterNot(_ == term1)) :+ prinFormula2), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = ImpTRalType
          def aux = (term1::Nil)::Nil
          def prin = prinFormula1::prinFormula2::Nil
          override def name = "\u2283 T"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == ImpTRalType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a::Nil)::Nil) = pr.aux
    val (p1::p2::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a.asInstanceOf[LabelledFormulaOccurrence], p1.asInstanceOf[LabelledFormulaOccurrence]), p2.asInstanceOf[LabelledFormulaOccurrence])
  }
  else None
}


object AFactorT {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, term2ocs : Seq[LabelledFormulaOccurrence]) = {
    s1.root.l_succedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formula 1 not contained in the right part of the sequent")
      case Some(term1) =>
        val fterms = term2ocs.map(occ => s1.root.l_succedent.find(_ == occ)).toList
        val terms = for (t <- fterms) yield {
          require(t.nonEmpty, "Could not find contracted formula in succedent!")
          val t_ = t.get
          require(term1.formula == t_.formula, "Contracted formulas must be equal!")
          t_
        }

        require(isAtom(term1.formula) , "Can only contract atom formulas!")
        val f = term1.formula
        val allaux = term1oc +: term2ocs
        val prinFormula1 = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1 :: terms ).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent), createContext(s1.root.succedent filterNot(allaux.contains(_))) ++ List(prinFormula1)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = AFactorTType
          def aux = (term1 :: terms)::Nil
          def prin = prinFormula1::Nil
          override def name = "c T"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == AFactorTType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::aux)::Nil) = pr.aux
    val (p1::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a1.asInstanceOf[LabelledFormulaOccurrence], aux.asInstanceOf[List[LabelledFormulaOccurrence]], p1.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}

object AFactorF {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, term2ocs : Seq[LabelledFormulaOccurrence]) = {
    s1.root.l_antecedent.find(x => x == term1oc) match {
      case None =>
        throw new ResolutionRuleCreationException("Auxiliary formula 1 not contained in the right part of the sequent")
      case Some(term1) =>
        val fterms = term2ocs.map(occ => s1.root.l_antecedent.find(_ == occ)).toList
        val terms = for (t <- fterms) yield {
          require(t.nonEmpty, "Could not find contracted formula in antecedent!")
          val t_ = t.get
          require(term1.formula == t_.formula, "Contracted formulas must be equal!")
          t_
        }

        require(isAtom(term1.formula) , "Can only contract atom formulas!")
        val f = term1.formula
        val allaux = term1oc +: term2ocs
        val prinFormula1 = term1.factory.createFormulaOccurrence( betaNormalize( f ), term1::terms).asInstanceOf[LabelledFormulaOccurrence]
        new UnaryAGraph[LabelledSequent](new LabelledSequent(createContext(s1.root.antecedent filterNot(allaux.contains(_))) ++ List(prinFormula1), createContext(s1.root.succedent)), s1)
          with RalResolutionProof[V] with UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas  {
          def rule = AFactorFType
          def aux = (term1 :: terms)::Nil
          def prin = prinFormula1::Nil
          override def name = "c F"
        }
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == AFactorFType ) {
    val pr = proof.asInstanceOf[UnaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::aux)::Nil) = pr.aux
    val (p1::Nil) = pr.prin
    Some((pr.root.asInstanceOf[LabelledSequent], pr.uProof.asInstanceOf[RalResolutionProof[V]], a1.asInstanceOf[LabelledFormulaOccurrence], aux.asInstanceOf[List[LabelledFormulaOccurrence]], p1.asInstanceOf[LabelledFormulaOccurrence]))
  }
  else None
}


object ParaT {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], s2: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, term2oc : LabelledFormulaOccurrence, para_formula : HOLFormula) = {
    val term1ops = s1.root.succedent.find(x => x == term1oc)
    val term2ops = s2.root.succedent.find(x => x == term2oc)
    (term1ops, term2ops) match {
      case (Some(occ1@LabelledFormulaOccurrence(term1, anc1, label1)),
            Some(occ2@LabelledFormulaOccurrence(term2, anc2, label2))) =>
        require(label1 == label2, "Paramodulation requires the labels to match, but we have "+label1+" and "+label2)
        val flip = term1 match {
          case Equation(s,t) =>
            (EquationVerifier(s,t, term2, para_formula ), EquationVerifier(t,s, term2, para_formula )) match {
              case (Different, Different) =>
                throw new Exception("Could not verify equation "+s+" = "+t+". Please check if "+para_formula+" really results from a replacement in "+term2)
              case (EqualModuloEquality(_), _) =>
                false
              case (_, EqualModuloEquality(_)) =>
                true
              case _ =>
                //this is a paramodulation of reflexifity
                false
            }
          case _ => throw new Exception("Expected equation as first argument of para rule, but got: "+term1)
        }

        val para_occ = new LabelledFormulaOccurrence(para_formula, List(occ1,occ2), label1)

        new BinaryAGraph[LabelledSequent](new LabelledSequent(
          createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent),
          createContext(s1.root.succedent filterNot(_ == term1oc)) ++ createContext(s2.root.succedent filterNot(_ == term2oc)) ++ List(para_occ) )
          , s1, s2)
          with RalResolutionProof[V] with BinaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with Flip {
          def rule = ParaTRalType
          def aux = List(term1oc, term2oc)::Nil
          val flipped = flip
          def prin = List(para_occ)
          override def name = "= T"

        }

      case (None, _)  =>
        throw  new ResolutionRuleCreationException("Could not find auxiliary occurrence"+term1oc+ " in first parent root "+s1)
      case _  =>
        throw  new ResolutionRuleCreationException("Could not find auxiliary occurrence"+term2oc+ " in second parent root "+s2)
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == ParaTRalType) {
    val r = proof.asInstanceOf[BinaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with Flip]
    val (List(a1,a2)::Nil) = r.aux
    Some((r.root, r.uProof1.asInstanceOf[RalResolutionProof[V]], r.uProof2.asInstanceOf[RalResolutionProof[V]],  a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], r.prin(0), r.flipped))
  }
  else None
}

object ParaF {
  def apply[V <: LabelledSequent](s1: RalResolutionProof[V], s2: RalResolutionProof[V], term1oc: LabelledFormulaOccurrence, term2oc : LabelledFormulaOccurrence, para_formula : HOLFormula) = {
    val term1ops = s1.root.succedent.find(x => x == term1oc)
    val term2ops = s2.root.antecedent.find(x => x == term2oc)
    (term1ops, term2ops) match {
      case (Some(occ1@LabelledFormulaOccurrence(term1, anc1, label1)),
            Some(occ2@LabelledFormulaOccurrence(term2, anc2, label2))) =>
        require(label1 == label2, "Paramodulation requires the labels to match, but we have "+label1+" and "+label2)
        val flip = term1 match {
          case Equation(s,t) =>
            (EquationVerifier(s,t, term2, para_formula ), EquationVerifier(t,s, term2, para_formula )) match {
              case (Different, Different) =>
                throw new Exception("Could not verify equation "+s+" = "+t+". Please check if "+para_formula+" really results from a replacement in "+term2)
              case (EqualModuloEquality(_), _) =>
                false
              case (_, EqualModuloEquality(_)) =>
                true
              case _ =>
                //this is a paramodulation of reflexifity
                false
            }
          case _ => throw new Exception("Expected equation as first argument of para rule, but got: "+term1)
        }

        val para_occ = new LabelledFormulaOccurrence(para_formula, List(occ1,occ2), label1)
        new BinaryAGraph[LabelledSequent](new LabelledSequent(
          createContext(s1.root.antecedent) ++ createContext(s2.root.antecedent filterNot(_ == term2oc)) ++ List(para_occ),
          createContext(s1.root.succedent filterNot(_ == term1oc)) ++ createContext(s2.root.succedent))
          , s1, s2)
          with RalResolutionProof[V] with BinaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with Flip {
          def rule = ParaFRalType
          def aux = List(term1oc, term2oc)::Nil
          def prin = List(para_occ)
          val flipped = flip
          override def name = "= F"
        }



      case (None, _)  =>
        throw  new ResolutionRuleCreationException("Could not find auxiliary occurrence"+term1oc+ " in first parent root "+s1)
      case _  =>
        throw  new ResolutionRuleCreationException("Could not find auxiliary occurrence"+term2oc+ " in second parent root "+s2)
    }
  }

  def unapply[V <: LabelledSequent](proof: ResolutionProof[V]) = if (proof.rule == ParaFRalType) {
    val r = proof.asInstanceOf[BinaryResolutionProof[V] with AuxiliaryFormulas with PrincipalFormulas with Flip]
    val (List(a1,a2)::Nil) = r.aux
    Some((r.root, r.uProof1.asInstanceOf[RalResolutionProof[V]], r.uProof2.asInstanceOf[RalResolutionProof[V]], a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], r.prin(0), r.flipped))
  }
  else None
}
