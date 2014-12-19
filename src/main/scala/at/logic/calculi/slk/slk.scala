package at.logic.calculi.slk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.language.schema._
import at.logic.language.schema.BetaReduction._
import at.logic.utils.ds.trees._
import at.logic.calculi.lk.{ContractionRightRuleType, ContractionLeftRuleType, CutRuleType, Axiom}
import at.logic.language.hol.HOLExpression

case object AndEquivalenceRule1Type extends UnaryRuleTypeA
case object AndEquivalenceRule2Type extends UnaryRuleTypeA
case object AndEquivalenceRule3Type extends UnaryRuleTypeA
case object OrEquivalenceRule1Type extends UnaryRuleTypeA
case object OrEquivalenceRule2Type extends UnaryRuleTypeA
case object OrEquivalenceRule3Type extends UnaryRuleTypeA
case object SchemaProofLinkRuleType extends NullaryRuleTypeA
case object TermEquivalenceRule1Type extends UnaryRuleTypeA
case object trsArrowRuleType extends UnaryRuleTypeA
case object foldRuleType extends UnaryRuleTypeA
case object ForallHyperLeftRuleType extends UnaryRuleTypeA
case object ExistsHyperLeftRuleType extends UnaryRuleTypeA
case object ForallHyperRightRuleType extends UnaryRuleTypeA
case object ExistsHyperRightRuleType extends UnaryRuleTypeA

// The following two classes are used to keep a global directory
// of proof schemata. Their definition is somewhat ad-hoc.

// base should have end-sequent seq where vars <- 0
// rec should have end-sequent seq where vars <- vars + 1

class SchemaProof(val name: String, val vars: List[IntVar], val seq: FSequent, val base: LKProof, val rec: LKProof) {
  val r_sub = Substitution(vars.map( v => (v,Succ(v))))
  val b_sub = Substitution(vars.map( v => (v,IntZero())))
  val r_res = FSequent( seq._1.map(f => r_sub(f.asInstanceOf[SchemaFormula])), seq._2.map(f => r_sub(f.asInstanceOf[SchemaFormula])) )
  val b_res = FSequent( seq._1.map(f => b_sub(f.asInstanceOf[SchemaFormula])), seq._2.map(f => b_sub(f.asInstanceOf[SchemaFormula])) )
}

object SchemaProofDB extends Iterable[(String, SchemaProof)] with TraversableOnce[(String, SchemaProof)] {
  val proofs = new scala.collection.mutable.HashMap[String, SchemaProof]
  val LinkTerms = new scala.collection.mutable.HashMap[String, List[SchemaExpression]]

  def clear = { proofs.clear;  LinkTerms.clear;}

  def get(name: String) = proofs(name)
  def getLinkTerms(name: String) = LinkTerms(name)
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
  def putLinkTerms(name: String,linkparams:  List[SchemaExpression]) = LinkTerms.put(name, linkparams)
  def iterator = proofs.iterator
}

trait SchemaProofLink {
  def link: String
  def indices: List[SchemaExpression]
}

object FOSchemaProofLinkRule {
  def apply(seq: FSequent, link_name: String, indices_ : List[SchemaExpression]) = {
    def createSide(side : Seq[SchemaFormula]) = {
      side.map(f =>factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence]))
    }
    new LeafTree[Sequent]( Sequent(createSide(seq._1.map(f => f.asInstanceOf[SchemaFormula])), createSide(seq._2.map(f => f.asInstanceOf[SchemaFormula])) ) ) with NullaryLKProof with SchemaProofLink {
      def rule = SchemaProofLinkRuleType
      def link = link_name
      def indices = indices_
    }
  }
  def apply(seq: FSequent, name: String, ind : IntegerTerm) : LeafTree[Sequent] with NullaryLKProof with SchemaProofLink= this.apply(seq, name, ind::Nil)
  def unapply( proof: LKProof ) =
    if (proof.rule == SchemaProofLinkRuleType) {
      val r = proof.asInstanceOf[NullaryLKProof with SchemaProofLink]
      Some((r.root, r.link, r.indices))
    }
    else None
}
object EXFOSchemaProofLinkRule  {
  def unapply( proof: LKProof ) =
    if (proof.rule == SchemaProofLinkRuleType) {
      val r = proof.asInstanceOf[NullaryLKProof with SchemaProofLink]
      Some((r.root, r.link, r.indices))
    }
    else None

}
//object ExtendedFOProofLinkRule {
//  def unapply( proof: LKProof ) =
//    if (proof.rule == SchemaProofLinkRuleType) {
//      val r = proof.asInstanceOf[NullaryLKProof with SchemaProofLink]
//      val intterm = r.indices(0)
//      Some((r.root, r.link, r.indices, intterm))
//    }
//    else None
//}

object SchemaProofLinkRule {
  def apply(seq: FSequent, link_name: String, indices_ : List[IntegerTerm])(implicit factory: FOFactory) = {
    def createSide(side : Seq[SchemaFormula]) = {
      side.map(f =>factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence]))
    }
    new LeafTree[Sequent]( Sequent(createSide(seq._1.map(f => f.asInstanceOf[SchemaFormula])), createSide(seq._2.map(f => f.asInstanceOf[SchemaFormula])) ) ) with NullaryLKProof with SchemaProofLink {
      def rule = SchemaProofLinkRuleType
      def link = link_name
      def indices = indices_
    }
  }
  def apply(seq: FSequent, name: String, ind : IntegerTerm)(implicit factory: FOFactory) : LeafTree[Sequent] with NullaryLKProof with SchemaProofLink= this.apply(seq, name, ind::Nil)
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
          val prinFormula = factory.createFormulaOccurrence( main, auxf +: Seq.empty[FormulaOccurrence] )
          def createSide( s : Seq[FormulaOccurrence] ) =
            if ( s.contains(auxf) )
              prinFormula +: createContext( s.filter(_ != auxf) )
            else
              createContext(s)
          new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
            with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
              def rule = AndEquivalenceRule1Type
              def aux = (auxf::Nil)::Nil
              def prin = prinFormula::Nil
              override def name = "\u2261:1"

            }
      }
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule1 must have a BigAnd as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}

object AndLeftEquivalenceRule1 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => AndEquivalenceRule1.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found in the left side for application of the AndLeftEquivalenceRule1 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == AndEquivalenceRule1Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val a1 = r.aux.head.head
      val p1 = r.prin.head
      if (r.root.antecedent.contains(p1))
        Some((r.uProof, r.root, a1, p1))
      else
        None
    }
    else
      None
}


// ---------------------------- And Equivalence 2 ---------------------------------------


object AndEquivalenceRule2 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigAnd(v, f, ub, lb) => {
        val prinFormula = factory.createFormulaOccurrence( main, auxf +: Seq.empty[FormulaOccurrence] )
        def createSide( s :  Seq[FormulaOccurrence] ) =
          if ( s.contains(auxf) )
            prinFormula +: createContext( s.filter(_ != auxf) )
          else
            createContext(s)

        new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = AndEquivalenceRule2Type
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
            override def name = "\u2261:2"
          }
      }
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule2 must have a BigAnd as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}

object AndLeftEquivalenceRule2 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}

// ---------------------------- And Equivalence 3 ---------------------------------------


object AndEquivalenceRule3 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigAnd(v, f, ub, lb) if ub == lb => {
        val prinFormula = factory.createFormulaOccurrence( main, auxf +: Seq.empty[FormulaOccurrence] )
        def createSide( s : Seq[FormulaOccurrence] ) =
          if ( s.contains(auxf) )
            prinFormula +: createContext( s.filter(_ != auxf) )
          else
            createContext(s)

        new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = AndEquivalenceRule3Type
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
            override def name = "\u2261:3"
          }
      }
      case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule3 must have a BigAnd as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}

object AndLeftEquivalenceRule3 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
          None
    }
    else
      None
}


// ---------------------------- Or Equivalence 1 ---------------------------------------

object OrEquivalenceRule1 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigOr(v, f, ub, Succ(lb)) => {
        val prinFormula = factory.createFormulaOccurrence( main, auxf +: Seq.empty[FormulaOccurrence] )
        def createSide( s : Seq[FormulaOccurrence] ) =
          if ( s.contains(auxf) )
            prinFormula +: createContext( s.filter(_ != auxf) )
          else
            createContext(s)

        new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
          with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
            def rule = OrEquivalenceRule1Type
            def aux = (auxf::Nil)::Nil
            def prin = prinFormula::Nil
            override def name = "\u2261:1"
          }
      }
      case _ => throw new LKRuleCreationException("Main formula of OrEquivalenceRule1 must have a BigOr as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the OrEquivalenceRule1 with the given formula")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == OrEquivalenceRule1Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}

object OrRightEquivalenceRule1 {
  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
    else
      None
   }
   else
     None
}

object OrLeftEquivalenceRule1 {
  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
    else
      None
  }
  else
    None
}

// ---------------------------- Or Equivalence 2 ---------------------------------------

object OrEquivalenceRule2 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigOr(v, f, ub, lb) => {
          val prinFormula = factory.createFormulaOccurrence( main, auxf +: Seq.empty[FormulaOccurrence] )
          def createSide( s : Seq[FormulaOccurrence] ) =
            if ( s.contains(auxf) )
              prinFormula +: createContext( s.filter(_ != auxf) )
            else
              createContext(s)

          new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
            with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
              def rule = OrEquivalenceRule2Type
              def aux = (auxf::Nil)::Nil
              def prin = prinFormula::Nil
              override def name = "\u2261:2"
            }
      }
      case _ => throw new LKRuleCreationException("Main formula of OrEquivalenceRule2 must have a BigOr as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}

object OrLeftEquivalenceRule2 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}


// ---------------------------- Or Equivalence 3 ---------------------------------------

object OrEquivalenceRule3 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    main match {
      case BigOr(v, f, ub, lb) if ub == lb => {
          val prinFormula = factory.createFormulaOccurrence( main, auxf  +: Seq.empty[FormulaOccurrence] )
          def createSide( s : Seq[FormulaOccurrence] ) =
            if ( s.contains(auxf) )
              prinFormula +: createContext( s.filter(_ != auxf) )
            else
              createContext(s)

          new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
            with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
              def rule = OrEquivalenceRule3Type
              def aux = (auxf::Nil)::Nil
              def prin = prinFormula::Nil
              override def name = "\u2261:3"
            }
      }
      case _ => throw new LKRuleCreationException("Main formula of OREquivalenceRule3 must have a BigOr as head symbol.")
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the OrEquivalenceRule3 with the given formula")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == OrEquivalenceRule3Type) {
      val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ((a1::Nil)::Nil) = r.aux
      val (p1::Nil) = r.prin
      Some((r.uProof, r.root, a1, p1))
    }
    else None
}


object OrRightEquivalenceRule3 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}

object OrLeftEquivalenceRule3 {
   def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
      else
        None
    }
    else
      None
}

// TODO: some preprocessing should be done, i.e. auxf.formula ->>_{\beta} main
object TermEquivalenceRule1 {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    val prinFormula = factory.createFormulaOccurrence( main, auxf::Nil)
    def createSide( s : Seq[FormulaOccurrence] ) =
      if ( s.contains(auxf) )
        prinFormula +: createContext( s.filter(_ != auxf) )
      else
        createContext(s)

    new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = TermEquivalenceRule1Type
      def aux = (auxf::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "def:1"
    }
  }


  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the OrEquivalenceRule3 with the given formula")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == TermEquivalenceRule1Type) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1))
  }
  else None
}


object TermRightEquivalenceRule1 {
  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.succedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => TermEquivalenceRule1.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the TermEquivalenceRule1 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == TermEquivalenceRule1Type) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    if (r.root.succedent.contains(p1))
      Some((r.uProof, r.root, a1, p1))
    else
      None
  }
  else
    None
}

object TermLeftEquivalenceRule1 {
  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent).filter(x => x.formula == auxf)).toList match {
      case (x::_) => TermEquivalenceRule1.apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the TermEquivalenceRule1 with the given formula")
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == TermEquivalenceRule1Type) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    if (r.root.antecedent.contains(p1))
      Some((r.uProof, r.root, a1, p1))
    else
      None
  }
  else
    None
}

object sCutRule {
  def apply(s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc)
    val sequent = getSequent(s1.root, s2.root, term1, term2)

    new BinaryTree[Sequent](sequent, s1, s2)
      with BinaryLKProof with AuxiliaryFormulas {
      def rule = CutRuleType
      def aux = (term1::Nil)::(term2::Nil)::Nil
      override def name = "cut"
    }
  }
  def apply(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, s2, term1oc, term2oc)
    getSequent(s1, s2, term1, term2)
  }
  // convenient method to choose the first two formulas
  def apply(s1: LKProof, s2: LKProof, term: SchemaFormula): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas  = {
    val succ = s1.root.succedent.filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(term)).toList
    val ant = s2.root.antecedent.filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(term)).toList
    (succ, ant) match {
      case ((x::_),(y::_)) => apply(s1, s2, x, y)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    }
  }
  private def getTerms(s1: Sequent, s2: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    val term2op = s2.antecedent.find(_ == term2oc)
    if (term1op == None || term2op == None) {
      val s1str = s1.succedent.head.toString()
      val s2str = s2.antecedent.head.toString()
      val t1str = term1oc.asInstanceOf[FormulaOccurrence].formula.toString()
      val t2str = term2oc.asInstanceOf[FormulaOccurrence].formula.toString()
      val str = "s1: " + s1str + "\ns2: " + s2str + "\nt1: " + t1str + "\nt2: " + t2str + "\n"
      throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent\n" + str)
    }
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      if (unfoldSFormula(term1.formula.asInstanceOf[SchemaFormula]) != unfoldSFormula(term2.formula.asInstanceOf[SchemaFormula])) throw new LKRuleCreationException("Formulas to be cut are not identical")
      else {
        (term1, term2)
      }
    }
  }
  private def getSequent(s1: Sequent, s2: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val ant1 = createContext(s1.antecedent)
    val ant2 = createContext(s2.antecedent.filterNot(_ == term2))
    val antecedent = ant1 ++ ant2
    val suc1 = createContext(s1.succedent.filterNot(_ == term1))
    val suc2 = createContext(s2.succedent)
    val succedent = suc1 ++ suc2
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == CutRuleType) {
    val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas]
    val ((a1::Nil)::(a2::Nil)::Nil) = r.aux
    Some((r.uProof1, r.uProof2, r.root, a1, a2.asInstanceOf[SchemaFormula]))
  }
  else None
}



object sContractionLeftRule {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term1, term2, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = ContractionLeftRuleType
      def aux = (term1::term2::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "c:l"
    }
  }
  def apply(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term1, term2, prinFormula)
  }
  // convenient method to choose the first two formulas
  def apply(s1: LKProof, term1: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
    (s1.root.antecedent.filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(term1))).toList match {
      case (x::y::_) => apply(s1, x, y)
      case _ => throw new LKRuleCreationException("No matching formulas found to contract.")
    }
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    val term2op = s1.antecedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the left part of the sequent")
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      if (unfoldSFormula(term1.formula.asInstanceOf[SchemaFormula]) != unfoldSFormula(term2.formula.asInstanceOf[SchemaFormula])) 
        throw new LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula.toString + ", term2.formula = " + term2.formula.toString)
      else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
      else {
        (term1, term2)
      }
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula.asInstanceOf[SchemaFormula]
    term1.factory.createFormulaOccurrence(holterm1, term1::term2::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val ant1 = createContext(s1.antecedent.filterNot(x => x == term1 || x == term2))
    val antecedent = ant1 :+ prinFormula
    val succedent = createContext(s1.succedent)
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ContractionLeftRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::a2::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, a2.asInstanceOf[SchemaFormula], p1))
  }
  else None
}


object sContractionRightRule {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1.root, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    val sequent = getSequent(s1.root, term1, term2, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = ContractionRightRuleType
      def aux = (term1::term2::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "c:r"
    }
  }
  def apply(s1: Sequent, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val (term1, term2) = getTerms(s1, term1oc, term2oc)
    val prinFormula = getPrinFormula(term1, term2)
    getSequent(s1, term1, term2, prinFormula)
  }
  // convenient method to choose the first two formulas
  def apply(s1: LKProof, term1: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
    (s1.root.succedent.filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(term1))).toList match {
      case (x::y::_) => apply(s1, x, y)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    }
  }
  private def getTerms(s1 : Sequent, term1oc : FormulaOccurrence, term2oc : FormulaOccurrence) = {
    val term1op = s1.succedent.find(_ == term1oc)
    val term2op = s1.succedent.find(_ == term2oc)
    if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val term1 = term1op.get
      val term2 = term2op.get
      if (unfoldSFormula(term1.formula.asInstanceOf[SchemaFormula]) != unfoldSFormula(term2.formula.asInstanceOf[SchemaFormula])) 
        throw new LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula.toString + ", term2.formula = " + term2.formula.toString)
      else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
      else {
        (term1, term2)
      }
    }
  }
  private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
    val holterm1 = term1.formula.asInstanceOf[SchemaFormula]
    term1.factory.createFormulaOccurrence(holterm1, term1::term2::Nil)
  }
  private def getSequent(s1: Sequent, term1: FormulaOccurrence, term2: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent)
    val suc1 = createContext(s1.succedent.filterNot(x =>  x == term1 || x == term2))
    val succedent = suc1 :+ prinFormula
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ContractionRightRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::a2::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, a2.asInstanceOf[SchemaFormula], p1))
  }
  else None
}


//----------------------- trsArrowRule ------------------

object trsArrowRule {
  def apply(s1: LKProof, auxf: FormulaOccurrence) = {
    val prinFormula = factory.createFormulaOccurrence( unfoldSFormula(auxf.formula.asInstanceOf[SchemaFormula]), auxf  +: Seq.empty[FormulaOccurrence] )
    def createSide( s : Seq[FormulaOccurrence] ) =
      if ( s.contains(auxf) )
        prinFormula +: createContext( s.filter(_ != auxf) )
      else
        createContext(s)

    new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = trsArrowRuleType
      def aux = (auxf::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "\u21A0"
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(auxf))).toList match {
      case (x::_) => apply(s1, x)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the trsArrowRule with the given formula")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == trsArrowRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1))
  }
  else None
}

object trsArrowRightRule {
  def apply(s1: LKProof, auxf: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.succedent).filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(auxf))).toList match {
      case (x::_) => trsArrowRule.apply(s1, x)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the trsArrowRightRule with the given formula")
    }
  }
  def apply(s1: LKProof, a: SchemaFormula, main: SchemaFormula) = {
    val auxf = (s1.root.succedent).filter(x => x.formula == a).head
    val prinFormula = factory.createFormulaOccurrence( main, auxf  +: Seq.empty[FormulaOccurrence] )
    def createSide( s : Seq[FormulaOccurrence] ) =
      if ( s.contains(auxf) )
        prinFormula +: createContext( s.filter(_ != auxf) )
      else
        createContext(s)

    new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = trsArrowRuleType
      def aux = (auxf::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "\u21A0:r"
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == trsArrowRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    if (r.root.succedent.contains(p1))
      Some((r.uProof, r.root, a1, p1))
    else
      None
  }
  else
    None
}

object trsArrowLeftRule {
  def apply(s1: LKProof, auxf: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent).filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(auxf))).toList match {
      case (x::_) => trsArrowRule.apply(s1, x)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences in the left side found for application of the trsArrowLeftRule with the given formula")
    }
  }
  def apply(s1: LKProof, a: SchemaFormula, main: SchemaFormula) = {
    val auxf = (s1.root.antecedent).filter(x => x.formula == a).head
    val prinFormula = factory.createFormulaOccurrence( main, auxf  +: Seq.empty[FormulaOccurrence] )
    def createSide( s : Seq[FormulaOccurrence] ) =
      if ( s.contains(auxf) )
        prinFormula +: createContext( s.filter(_ != auxf) )
      else
        createContext(s)

    new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = trsArrowRuleType
      def aux = (auxf::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "\u21A0:l"
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == trsArrowRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    if (r.root.antecedent.contains(p1))
      Some((r.uProof, r.root, a1, p1))
    else
      None
  }
  else
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
    case trsArrowRule(up, r, a, p)      => Some((trsArrowRuleType, up, r, a::Nil, p))
    case foldRule(up, r, a, p)          => Some((foldRuleType, up, r, a::Nil, p))
    case _ => None
  }
}



// TODO: refactor somewhere else
// checks whether the SchemaProofLink calls are correct
// w.r.t. the SchemaProofDB, if not throws an Exception
object checkProofLinks {
  def apply(p: LKProof):Unit = p match {
    case Axiom(so) => {}
    case UnaryLKProof(_,upperProof,_,_,_) => checkProofLinks( upperProof )
    case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux1, aux2, _) => 
      checkProofLinks( upperProofLeft ); checkProofLinks( upperProofRight )
    case UnarySchemaProof(_,upperProof,_,_,_) => checkProofLinks( upperProof )
    case SchemaProofLinkRule(so, name, indices) => {
      val ps = SchemaProofDB.get( name )
      val sub = Substitution(ps.vars.zip(indices))
      require(ps.seq equals FSequent(so.toFSequent._1.map(f => sub(f.asInstanceOf[SchemaFormula])), so.toFSequent._2.map(f => sub(f.asInstanceOf[SchemaFormula])) ) )
    }
  }
}



//----------------------- foldRule ------------------

object foldRule {
  def apply(s1: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
    val prinFormula = factory.createFormulaOccurrence( main, auxf  +: Seq.empty[FormulaOccurrence] )
    def createSide( s : Seq[FormulaOccurrence] ) =
      if ( s.contains(auxf) )
        prinFormula +: createContext( s.filter(_ != auxf) )
      else
        createContext(s)

    new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = foldRuleType
      def aux = (auxf::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "↞"
    }
  }

  def apply(s1: LKProof, auxf: SchemaFormula, main: SchemaFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    ((s1.root.antecedent ++ s1.root.succedent).filter(x => unfoldSFormula(x.formula.asInstanceOf[SchemaFormula]) == unfoldSFormula(auxf))).toList match {
      case (x::_) => apply(s1, x, main)
      case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the foldRule with the given formula")
    }
  }

  def unapply(proof: LKProof) =  if (proof.rule == foldRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1))
  }
  else None
}

object foldRightRule {
  def apply(s1: LKProof, a: SchemaFormula, main: SchemaFormula) = {
    val auxf = (s1.root.succedent).filter(x => x.formula == a).head
    val prinFormula = factory.createFormulaOccurrence( main, auxf  +: Seq.empty[FormulaOccurrence] )
    def createSide( s : Seq[FormulaOccurrence] ) =
      if ( s.contains(auxf) )
        prinFormula +: createContext( s.filter(_ != auxf) )
      else
        createContext(s)

    new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = foldRuleType
      def aux = (auxf::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "↞:r"
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == foldRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    if (r.root.succedent.contains(p1))
      Some((r.uProof, r.root, a1, p1))
    else
      None
  }
  else
    None
}

object foldLeftRule {
  def apply(s1: LKProof, a: SchemaFormula, main: SchemaFormula) = {
    val auxf = (s1.root.antecedent).filter(x => x.formula == a).head
    val prinFormula = factory.createFormulaOccurrence( main, auxf  +: Seq.empty[FormulaOccurrence] )
    def createSide( s : Seq[FormulaOccurrence] ) =
      if ( s.contains(auxf) )
        prinFormula +: createContext( s.filter(_ != auxf) )
      else
        createContext(s)

    new UnaryTree[Sequent]( new Sequent( createSide(s1.root.antecedent), createSide( s1.root.succedent)), s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = foldRuleType
      def aux = (auxf::Nil)::Nil
      def prin = prinFormula::Nil
      override def name = "↞:l"
    }
  }
  def unapply(proof: LKProof) = if (proof.rule == foldRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    if (r.root.antecedent.contains(p1))
      Some((r.uProof, r.root, a1, p1))
    else
      None
  }
  else
    None
}


object ForallHyperLeftRule {
  def apply(s1: LKProof, aux: SchemaFormula, main: SchemaFormula, term: SchemaExpression) : LKProof = {
    s1.root.antecedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, term )
      case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula.")
    }
  }

  def apply(s1: LKProof, term1oc: FormulaOccurrence, main: SchemaFormula, term: SchemaExpression) : LKProof = {
    val (aux_fo, aux_form) = getTerms(s1.root, term1oc, main, term)
    val prinFormula = getPrinFormula(main, aux_fo)
    val sequent = getSequent(s1.root, aux_fo, prinFormula)

    new UnaryTree[Sequent](sequent, s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
      def rule = ForallHyperLeftRuleType
      def aux = (aux_fo::Nil)::Nil
      def prin = prinFormula::Nil
      def subst = term
      override def name = "\u2200 hyp:l"
    }
  }
  def apply(s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, term: SchemaExpression) = {
    val (aux_fo, aux_form) = getTerms(s1, term1oc, main, term)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, term: SchemaExpression) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    if (term1op == None) {
      def o2s(occ:FormulaOccurrence) = occ +" formula="+occ.formula+ " ancestors="+occ.parents
      println(o2s(term1oc.asInstanceOf[FormulaOccurrence]))
      //s1.antecedent.head.ancestors foreach ( (x:FormulaOccurrence) => println(o2s(x)))
      throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    }
    else {
      val aux_fo = term1op.get
      (aux_fo, aux_fo.formula)
    }
  }
  private def getPrinFormula(main: SchemaFormula, aux_fo: FormulaOccurrence) = {
    aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
  }
  private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val ant = createContext(s1.antecedent.filterNot(_ == aux_fo))
    val antecedent = ant :+ prinFormula
    val succedent = createContext(s1.succedent)
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ForallHyperLeftRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.subst))
  }
  else None
}


object ExistsHyperRightRule {
  def apply(s1: LKProof, aux: SchemaFormula, main: SchemaFormula, term: SchemaExpression) : LKProof = {
    s1.root.succedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, term )
      case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
    }
  }

  def computeAux( main: SchemaFormula, term: SchemaExpression ) = main match {
    case ExVar( _, sub ) => betaNormalize( SchemaApp( sub, term ) ).asInstanceOf[SchemaFormula]
    case _ => throw new LKRuleCreationException("Main formula of ExistsRightRule must have a universal quantifier as head symbol.")
  }

  def apply(s1: LKProof, term1oc: FormulaOccurrence, main: SchemaFormula, term: SchemaExpression) : LKProof = {
    val aux_fo = getTerms(s1.root, term1oc, main, term)
    val prinFormula = getPrinFormula(main, aux_fo)
    val sequent = getSequent(s1.root, aux_fo, prinFormula)

    new UnaryTree[Sequent](sequent, s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm {
      def rule = ExistsHyperRightRuleType
      def aux = (aux_fo::Nil)::Nil
      def prin = prinFormula::Nil
      def subst = term
      override def name = "\u2203 hyp:r"
    }
  }
  def apply(s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, term: SchemaExpression) = {
    val aux_fo = getTerms(s1, term1oc, main, term)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, term: SchemaExpression) = {
    val term1op = s1.succedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val aux_fo = term1op.get
//      assert( computeAux( main, term ).syntaxEquals( aux_fo.formula ), computeAux( main, term ).toStringSimple + " is not " + aux_fo.formula.toStringSimple )
      aux_fo
    }
  }
  private def getPrinFormula(main: SchemaFormula, aux_fo: FormulaOccurrence) = {
    aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
  }
  private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent)
    val suc = createContext(s1.succedent.filterNot(_ == aux_fo))
    val succedent = suc :+ prinFormula
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ExistsHyperRightRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with SubstitutionTerm]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.subst))
  }
  else None
}

object ForallHyperRightRule {
  def apply(s1: LKProof, aux: SchemaFormula, main: SchemaFormula, eigen_var: SchemaVar) : LKProof =
    s1.root.succedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, eigen_var )
      case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
    }

  def apply( s1: LKProof, term1oc: FormulaOccurrence, main: SchemaFormula, eigen_var: SchemaVar ) : LKProof = {
    val aux_fo = getTerms(s1.root, term1oc, main, eigen_var)
    val prinFormula = getPrinFormula(main, aux_fo)
    val sequent = getSequent(s1.root, aux_fo, prinFormula)

    new UnaryTree[Sequent](sequent, s1 )
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
      def rule = ForallHyperRightRuleType
      def aux = (aux_fo::Nil)::Nil
      def prin = prinFormula::Nil
      def eigenvar = eigen_var
      override def name = "\u2200 hyp:r"
    }
  }
  def apply( s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, eigen_var: SchemaVar ) = {
    val aux_fo = getTerms(s1, term1oc, main, eigen_var)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }
  private def getTerms(s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, eigen_var: SchemaVar) = {
    val term1op = s1.succedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxiliary formulas are not contained in the right part of the sequent")
    else {
      val aux_fo = term1op.get
      main match {
        case AllVar( _, sub ) => {
          // eigenvar condition
          assert( ( s1.antecedent ++ (s1.succedent.filterNot(_ == aux_fo)) ).forall( fo => !freeVariables(fo.formula.asInstanceOf[SchemaFormula]).contains( eigen_var ) ),
            "Eigenvariable " + eigen_var.toString + " occurs in context " + s1.toString )
          // correct auxiliary formula
          //            println("ForallRightRule")
          //            println("eigen_var = "+eigen_var)
          //            println("betaNormalize( App( sub, eigen_var ): " + betaNormalize( App( sub, eigen_var )))
          //            println("aux_fo: " + aux_fo.formula)
          // TODO: uncomment assert( betaNormalize( SchemaApp( sub, eigen_var ) ) == aux_fo.formula , "\n\nassert 2 in getTerms of ForallRight fails!\n\n")
          aux_fo
        }
        case _ => throw new LKRuleCreationException("Main formula of ForallRightRule must have a universal quantifier as head symbol.")
      }
    }
  }
  private def getPrinFormula(main: SchemaFormula, aux_fo: FormulaOccurrence) = {
    aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
  }
  private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val antecedent = createContext(s1.antecedent)
    val suc = createContext(s1.succedent.filterNot(_ == aux_fo))
    val succedent = suc :+ prinFormula
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ForallHyperRightRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.eigenvar))
  }
  else None
}

object ExistsHyperLeftRule {
  def apply(s1: LKProof, aux: SchemaFormula, main: SchemaFormula, eigen_var: SchemaVar) : LKProof =
    s1.root.antecedent.filter( x => x.formula == aux ).toList match {
      case (x::_) => apply( s1, x, main, eigen_var )
      case _ => throw new LKRuleCreationException("No matching formula occurrence found for application of the rule with the given auxiliary formula")
    }

  def apply( s1: LKProof, term1oc: FormulaOccurrence, main: SchemaFormula, eigen_var: SchemaVar ) : LKProof = {
    val aux_fo = getTerms(s1.root, term1oc, main, eigen_var)
    val prinFormula = getPrinFormula(main, aux_fo)
    val sequent = getSequent(s1.root, aux_fo, prinFormula)

    new UnaryTree[Sequent](sequent, s1)
      with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable {
      def rule = ExistsHyperLeftRuleType
      def aux = (aux_fo::Nil)::Nil
      def prin = prinFormula::Nil
      def eigenvar = eigen_var
      override def name = "\u2203 hyp:l"
    }
  }
  def apply( s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, eigen_var: SchemaVar ) = {
    val aux_fo = getTerms(s1, term1oc, main, eigen_var)
    val prinFormula = getPrinFormula(main, aux_fo)
    getSequent(s1, aux_fo, prinFormula)
  }
  private def getTerms( s1: Sequent, term1oc: FormulaOccurrence, main: SchemaFormula, eigen_var: SchemaVar ) = {
    val term1op = s1.antecedent.find(_ == term1oc)
    if (term1op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
    else {
      val aux_fo = term1op.get
      main match {
        case ExVar( _, sub ) => {
          // eigenvar condition
          assert( ( (s1.antecedent.filterNot(_ == aux_fo)) ++ s1.succedent ).forall( fo => !freeVariables(fo.formula.asInstanceOf[SchemaFormula]).contains( eigen_var ) ),
            "Eigenvariable " + eigen_var.toString + " occurs in context " + s1.toString )
          // correct auxiliary formula
          //            assert( betaNormalize( App( sub, eigen_var ) ) == aux_fo.formula )
          aux_fo
        }
        case _ => throw new LKRuleCreationException("Main formula of ExistsLeftRule must have an existential quantifier as head symbol.")
      }
    }
  }
  private def getPrinFormula(main: SchemaFormula, aux_fo: FormulaOccurrence) = {
    aux_fo.factory.createFormulaOccurrence(main, aux_fo::Nil)
  }
  private def getSequent(s1: Sequent, aux_fo: FormulaOccurrence, prinFormula: FormulaOccurrence) = {
    val ant = createContext(s1.antecedent.filterNot(_ == aux_fo))
    val antecedent = ant :+ prinFormula
    val succedent = createContext((s1.succedent))
    Sequent(antecedent, succedent)
  }
  def unapply(proof: LKProof) = if (proof.rule == ExistsHyperLeftRuleType) {
    val r = proof.asInstanceOf[UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas with Eigenvariable]
    val ((a1::Nil)::Nil) = r.aux
    val (p1::Nil) = r.prin
    Some((r.uProof, r.root, a1, p1, r.eigenvar))
  }
  else None
}
