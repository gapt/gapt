package at.logic.calculi.slk

import at.logic.language.hol.HOLExpression
import at.logic.language.lambda.substitutions.Substitution
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
case object OrEquivalenceRule1Type extends UnaryRuleTypeA
case object OrEquivalenceRule2Type extends UnaryRuleTypeA
case object OrEquivalenceRule3Type extends UnaryRuleTypeA
case object SchemaProofLinkRuleType extends NullaryRuleTypeA

// The following two classes are used to keep a global directory
// of proof schemata. Their definition is somewhat ad-hoc.

// base should have end-sequent seq where vars <- 0
// rec should have end-sequent seq where vars <- vars + 1
class SchemaProof(val name: String, val vars: List[IntVar], val seq: Sequent, val base: LKProof, val rec: LKProof)
{
  {
    // FIXME: why are these casts needed?
    val r_sub = Substitution(vars.map( v => (v,Succ(v).asInstanceOf[HOLExpression])))
    val b_sub = Substitution(vars.map( v => (v,IntZero().asInstanceOf[HOLExpression])))
    val r_res = substitute(r_sub, seq)
    val b_res = substitute(b_sub, seq)
    require( rec.root.getSequent == r_res, rec.root.getSequent + " != " + r_res )
    require( base.root.getSequent == b_res, base.root.getSequent + " != " + b_res )
  }
}

object SchemaProofDB extends Iterable[(String, SchemaProof)] with TraversableOnce[(String, SchemaProof)] {
  val proofs = new scala.collection.mutable.HashMap[String, SchemaProof]

  def get(name: String) = proofs(name)

  // Compute a map between sets of FOs from
  // SchemaProofLinkRules and end-sequents of proof.base, proof.rec
  // and CutConfigurations, such that the CutConfigurations are
  // compatible between the different LKS-proofs.
  // Should only be called once all relevant proofs are
  // included (so that every SchemaProofLinkRule can be resolved).
  //
  // TODO: maybe put this somewhere else, seems to fit better with
  // the code that compute the characteristic clause set.
  def computeCutConfigs() = {
    // TODO: implement
  }

  def put(proof: SchemaProof) = proofs.put(proof.name, proof)
  def iterator = proofs.iterator
}

trait SchemaProofLink {
  def link: String
  def indices: List[IntegerTerm]
}

object SchemaProofLinkRule {
  def apply(seq: Sequent, link_name: String, indices_ : List[IntegerTerm])(implicit factory: FOFactory) = {
    def createSide(side : List[SchemaFormula]) = side.foldLeft(Set.empty[FormulaOccurrence])((st, form) => st + factory.createPrincipalFormulaOccurrence(form, Nil, st))
    new LeafTree[SequentOccurrence]( SequentOccurrence(createSide(seq.antecedent.asInstanceOf[List[SchemaFormula]]), createSide(seq.succedent.asInstanceOf[List[SchemaFormula]]) ) ) with NullaryLKProof with SchemaProofLink {
      def rule = SchemaProofLinkRuleType
      def link = link_name
      def indices = indices_
    }
  }
  def apply(seq: Sequent, name: String, ind : IntegerTerm)(implicit factory: FOFactory) : LeafTree[SequentOccurrence] with NullaryLKProof with SchemaProofLink= this.apply(seq, name, ind::Nil)
  def unapply( proof: LKProof ) =
    if (proof.rule == SchemaProofLinkRuleType) {
      val r = proof.asInstanceOf[NullaryLKProof with SchemaProofLink]
      Some((r.root, r.link, r.indices))
    }
    else None
  }


// ---------------------------- And Equivalence 1 ---------------------------------------

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
              def rule = AndEquivalenceRule1Type
              def aux = (auxf::Nil)::Nil
              def prin = prinFormula::Nil
            }
      }
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule1 must have a BigAnd as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the AndEquivalenceRule1 with the given formula")
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


object AndRightEquivalenceRule1 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => AndEquivalenceRule1.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the AndRightEquivalenceRule1 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == AndEquivalenceRule1Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      if (r.root.succedent.contains(p1))
        Some((r.uProof, r.root, a1, p1))
    }
    None
}

object AndLeftEquivalenceRule1 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => AndEquivalenceRule1.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found in the left side for application of the AndLeftEquivalenceRule1 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == AndEquivalenceRule1Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      if (r.root.antecedent.contains(p1))
        Some((r.uProof, r.root, a1, p1))
    }
    None
}


// ---------------------------- And Equivalence 2 ---------------------------------------


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
              def rule = AndEquivalenceRule2Type
              def aux = (auxf::Nil)::Nil
              def prin = prinFormula::Nil
            }
      }
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule2 must have a BigAnd as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the AndEquivalenceRule2 with the given formula")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == AndEquivalenceRule2Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object AndRightEquivalenceRule2 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => AndEquivalenceRule2.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the AndRightEquivalenceRule2 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == AndEquivalenceRule2Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      if (r.root.succedent.contains(p1))
        Some((r.uProof, r.root, a1, p1))
    }
    None
}

object AndLeftEquivalenceRule2 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => AndEquivalenceRule2.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found in the left side for application of the AndLeftEquivalenceRule2 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == AndEquivalenceRule2Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      if (r.root.antecedent.contains(p1))
        Some((r.uProof, r.root, a1, p1))
    }
    None
}

// ---------------------------- And Equivalence 3 ---------------------------------------


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

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the AndEquivalenceRule3 with the given formula")
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


//the next 2 rules specify in which side of the |- should be applied the AndEquvalence3 rule
object AndRightEquivalenceRule3 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => AndEquivalenceRule3.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the AndRightEquivalenceRule3 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == AndEquivalenceRule3Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      if (r.root.succedent.contains(p1))
        Some((r.uProof, r.root, a1, p1))
    }
    None
}

object AndLeftEquivalenceRule3 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => AndEquivalenceRule3.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found in the left side for application of the AndLeftEquivalenceRule3 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == AndEquivalenceRule3Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      if (r.root.antecedent.contains(p1))
        Some((r.uProof, r.root, a1, p1))
    }
    None
}


// ---------------------------- Or Equivalence 1 ---------------------------------------

object OrEquivalenceRule1 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigOr(v, f, ub, Succ(lb)) => {
          require( Or( BigOr( v, f, ub, lb ), betaNormalize( App(Abs(v, f), Succ(lb)) ).asInstanceOf[SchemaFormula] ) == auxf.formula )
          val prinFormula = PointerFOFactoryInstance.createPrincipalFormulaOccurrence( main, auxf::Nil )
          def createSide( s : Set[FormulaOccurrence] ) =
            if ( s.contains( auxf ) )
              createContext(s - auxf) + prinFormula
            else
              createContext(s)
          new UnaryTree[SequentOccurrence]( new SequentOccurrence( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
            with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
              def rule = OrEquivalenceRule1Type
              def aux = (auxf::Nil)::Nil
              def prin = prinFormula::Nil
            }
      }
      case _ => throw new LKRuleCreationException("Main formula of OrEquivalenceRule1 must have a BigOr as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the OrEquivalenceRule1 with the given formula")
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
   object OrRightEquivalenceRule1 {
     def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => OrEquivalenceRule1.apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the OrRightEquivalenceRule1 with the given formula")
      }
    }
    def unapply(proof: LKProof) = if (proof.rule == OrEquivalenceRule1Type) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        if (r.root.succedent.contains(p1))
          Some((r.uProof, r.root, a1, p1))
      }
      None
  }

  object OrLeftEquivalenceRule1 {
     def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => OrEquivalenceRule1.apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found in the left side for application of the OrLeftEquivalenceRule1 with the given formula")
      }
    }
    def unapply(proof: LKProof) = if (proof.rule == OrEquivalenceRule1Type) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        if (r.root.antecedent.contains(p1))
          Some((r.uProof, r.root, a1, p1))
      }
      None
  }

// ---------------------------- Or Equivalence 2 ---------------------------------------

  object OrEquivalenceRule2 {
    def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
      main match {
        case BigOr(v, f, ub, lb) => {
            require( Or( BigOr( v, f, Succ(ub), lb ), betaNormalize( App(Abs(v, f), ub) ).asInstanceOf[SchemaFormula] ) == auxf.formula )
            val prinFormula = PointerFOFactoryInstance.createPrincipalFormulaOccurrence( main, auxf::Nil )
            def createSide( s : Set[FormulaOccurrence] ) =
              if ( s.contains( auxf ) )
                createContext(s - auxf) + prinFormula
              else
                createContext(s)
            new UnaryTree[SequentOccurrence]( new SequentOccurrence( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                def rule = OrEquivalenceRule2Type
                def aux = (auxf::Nil)::Nil
                def prin = prinFormula::Nil
              }
        }
        case _ => throw new LKRuleCreationException("Main formula of OrEquivalenceRule2 must have a BigOr as head symbol.")
      }
    }

    def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the OrEquivalenceRule2 with the given formula")
      }
    }

    def unapply(proof: LKProof) =  if (proof.rule == OrEquivalenceRule2Type) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        Some((r.uProof, r.root, a1, p1))
      }
      else None
  }


   object OrRightEquivalenceRule2 {
     def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => OrEquivalenceRule2.apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the OrRightEquivalenceRule2 with the given formula")
      }
    }
    def unapply(proof: LKProof) = if (proof.rule == OrEquivalenceRule2Type) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        if (r.root.succedent.contains(p1))
          Some((r.uProof, r.root, a1, p1))
      }
      None
  }

  object OrLeftEquivalenceRule2 {
     def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => OrEquivalenceRule2.apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found in the left side for application of the OrLeftEquivalenceRule2 with the given formula")
      }
    }
    def unapply(proof: LKProof) = if (proof.rule == OrEquivalenceRule2Type) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        if (r.root.antecedent.contains(p1))
          Some((r.uProof, r.root, a1, p1))
      }
      None
  }


// ---------------------------- Or Equivalence 3 ---------------------------------------

  object OrEquivalenceRule3 {
    def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
      main match {
        case BigOr(v, f, ub, lb) if ub == lb => {
            require( betaNormalize( App(Abs(v, f), ub) ) == auxf.formula )
            val prinFormula = PointerFOFactoryInstance.createPrincipalFormulaOccurrence( main, auxf::Nil )
            def createSide( s : Set[FormulaOccurrence] ) =
              if ( s.contains( auxf ) )
                createContext(s - auxf) + prinFormula
              else
                createContext(s)
            new UnaryTree[SequentOccurrence]( new SequentOccurrence( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
              with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
                def rule = OrEquivalenceRule3Type
                def aux = (auxf::Nil)::Nil
                def prin = prinFormula::Nil
              }
        }
        case _ => throw new LKRuleCreationException("Main formula of OREquivalenceRule3 must have a BigOr as head symbol.")
      }
    }

    def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the AndEquivalenceRule3 with the given formula")
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


  object OrRightEquivalenceRule3 {
     def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => OrEquivalenceRule3.apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the OrRightEquivalenceRule3 with the given formula")
      }
    }
    def unapply(proof: LKProof) = if (proof.rule == OrEquivalenceRule3Type) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        if (r.root.succedent.contains(p1))
          Some((r.uProof, r.root, a1, p1))
      }
      None
  }

  object OrLeftEquivalenceRule3 {
     def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
        case (x::_) => OrEquivalenceRule3.apply(s1, x, main)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found in the left side for application of the OrLeftEquivalenceRule3 with the given formula")
      }
    }
    def unapply(proof: LKProof) = if (proof.rule == OrEquivalenceRule3Type) {
        val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
        val ((a1::Nil)::Nil) = r.aux
        val (p1::Nil) = r.prin
        if (r.root.antecedent.contains(p1))
          Some((r.uProof, r.root, a1, p1))
      }
      None
  }

//-------------------------------------------------------------------------------------------------

 // convenient extractors
  object UnarySchemaProof {
    def unapply(proof: LKProof) = proof match {
      case AndEquivalenceRule1(up, r, a, p) => Some((AndEquivalenceRule1Type, up, r, a::Nil, p))
      case AndEquivalenceRule2(up, r, a, p) => Some((AndEquivalenceRule2Type, up, r, a::Nil, p))
      case AndEquivalenceRule3(up, r, a, p) => Some((AndEquivalenceRule3Type, up, r, a::Nil, p))
      case OrEquivalenceRule1(up, r, a, p) => Some((OrEquivalenceRule1Type, up, r, a::Nil, p))
      case OrEquivalenceRule2(up, r, a, p) => Some((OrEquivalenceRule2Type, up, r, a::Nil, p))
      case OrEquivalenceRule3(up, r, a, p) => Some((OrEquivalenceRule3Type, up, r, a::Nil, p))
      case _ => None
    }
  }
