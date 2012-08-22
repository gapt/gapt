package at.logic.calculi.slk

import at.logic.language.hol.HOLExpression
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors._
import at.logic.language.schema._
import at.logic.utils.ds.trees._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.typedLambdaCalculus.{App, Abs}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import scala.collection.immutable.Seq
import at.logic.language.hol.{HOLFormula}
import at.logic.utils.traits.Occurrence
import at.logic.calculi.lk.propositionalRules.{ContractionRightRuleType, ContractionLeftRuleType, CutRuleType, Axiom}


case object AndEquivalenceRule1Type extends UnaryRuleTypeA
case object AndEquivalenceRule2Type extends UnaryRuleTypeA
case object AndEquivalenceRule3Type extends UnaryRuleTypeA
case object OrEquivalenceRule1Type extends UnaryRuleTypeA
case object OrEquivalenceRule2Type extends UnaryRuleTypeA
case object OrEquivalenceRule3Type extends UnaryRuleTypeA
case object SchemaProofLinkRuleType extends NullaryRuleTypeA
case object TermEquivalenceRule1Type extends UnaryRuleTypeA
case object trsArrowRuleType extends UnaryRuleTypeA

// The following two classes are used to keep a global directory
// of proof schemata. Their definition is somewhat ad-hoc.

// base should have end-sequent seq where vars <- 0
// rec should have end-sequent seq where vars <- vars + 1

//creates a siquent wich is not in a proof tree, i.e. it has not ancestor relation involved
object SingleSequent {
  def apply(ant: Seq[SchemaFormula], succ: Seq[SchemaFormula]) = {
      val new_ant = ant.map(f => factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence]))
      val new_succ = succ.map(f => factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence]))
      Sequent(new_ant, new_succ)
  }
}

class SchemaProof(val name: String, val vars: List[IntVar], val seq: FSequent, val base: LKProof, val rec: LKProof)
{
  {
    // FIXME: why are these casts needed?
    val r_sub = Substitution(vars.map( v => (v,Succ(v).asInstanceOf[HOLExpression])))
    val b_sub = Substitution(vars.map( v => (v,IntZero().asInstanceOf[HOLExpression])))
    val r_res = substitute(r_sub, seq)
    val b_res = substitute(b_sub, seq)

//    require( rec.root == r_res, rec.root + " != " + r_res )
//    require( base.root == b_res, base.root + " != " + b_res )
//
//    println("rec:")
//    rec.root.toFSequent()._1.foreach(f => println("\n"+f.toStringSimple))
//    print("|-")
//    rec.root.toFSequent()._2.foreach(f => println("\n"+f.toStringSimple))
//    println("r_res:")
//    r_res._1.foreach(f => println("\n"+f.toStringSimple))
//    print("|-")
//    r_res._2.foreach(f => println("\n"+f.toStringSimple))
//
//    require(rec.root.toFSequent() == r_res)
//    println("base:")
//    base.root.toFSequent()._1.foreach(f => println("\n"+f.toStringSimple))
//    print("|-")
//    base.root.toFSequent()._2.foreach(f => println("\n"+f.toStringSimple))
//    println("b_res:")
//    b_res._1.foreach(f => println("\n"+f.toStringSimple))
//    print("|-")
//    b_res._2.foreach(f => println("\n"+f.toStringSimple))
//    require(base.root.toFSequent() == b_res)
//    require( rec.root.antecedent.map(fo => fo.formula).toSet == seq.antecedent.map(fo => r_sub(fo.formula)).toSet)
//    require( rec.root.succedent.map(fo => fo.formula).toSet == seq.succedent.map(fo => r_sub(fo.formula)).toSet)
//    require( base.root.antecedent.map(fo => fo.formula).toSet == seq.antecedent.map(fo => b_sub(fo.formula)).toSet)
//    require( base.root.succedent.map(fo => fo.formula).toSet == seq.succedent.map(fo => b_sub(fo.formula)).toSet)
  }
}

object SchemaProofDB extends Iterable[(String, SchemaProof)] with TraversableOnce[(String, SchemaProof)] {
  val proofs = new scala.collection.mutable.HashMap[String, SchemaProof]

  def clear = proofs.clear

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

object FOSchemaProofLinkRule {
  def apply(seq: FSequent, link_name: String, indices_ : List[IntegerTerm]) = {
    def createSide(side : Seq[HOLFormula]) = {
      side.map(f =>factory.createFormulaOccurrence(f, Seq.empty[FormulaOccurrence]))
    }
    new LeafTree[Sequent]( Sequent(createSide(seq._1.map(f => f.asInstanceOf[HOLFormula])), createSide(seq._2.map(f => f.asInstanceOf[HOLFormula])) ) ) with NullaryLKProof with SchemaProofLink {
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
          require( And( BigAnd( v, f, ub, lb ), betaNormalize( App(Abs(v, f), Succ(lb)) ).asInstanceOf[SchemaFormula] ) == auxf.formula ||
                   And( betaNormalize( App(Abs(v, f), Succ(lb)) ).asInstanceOf[SchemaFormula], BigAnd( v, f, ub, lb )  ) == auxf.formula
                 )
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
          require( And( BigAnd( v, f, Succ(ub), lb ), betaNormalize( App(Abs(v, f), ub) ).asInstanceOf[SchemaFormula] ) == auxf.formula ||
                   And( betaNormalize( App(Abs(v, f), ub) ).asInstanceOf[SchemaFormula], BigAnd( v, f, Succ(ub), lb ) ) == auxf.formula
                  )
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
          require( betaNormalize( App(Abs(v, f), ub) ) == auxf.formula )
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
          require( Or( BigOr( v, f, ub, lb ), betaNormalize( App(Abs(v, f), Succ(lb)) ).asInstanceOf[SchemaFormula] ) == auxf.formula ||
                    Or( betaNormalize( App(Abs(v, f), Succ(lb)) ).asInstanceOf[SchemaFormula], BigOr( v, f, ub, lb ) ) == auxf.formula
                 )
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
            require( Or( BigOr( v, f, Succ(ub), lb ), betaNormalize( App(Abs(v, f), ub) ).asInstanceOf[SchemaFormula] ) == auxf.formula ||
                     Or( betaNormalize( App(Abs(v, f), ub) ).asInstanceOf[SchemaFormula], BigOr( v, f, Succ(ub), lb ) ) == auxf.formula
                   )
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
            require( betaNormalize( App(Abs(v, f), ub) ) == auxf.formula )
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
    def apply(s1: LKProof, auxf: FormulaOccurrence, main: HOLFormula) = {
      val prinFormula = factory.createFormulaOccurrence( main, auxf  +: Seq.empty[FormulaOccurrence] )
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


    def apply(s1: LKProof, auxf: HOLFormula, main: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
    def apply(s1: LKProof, auxf: HOLFormula, main: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
    def apply(s1: LKProof, auxf: HOLFormula, main: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
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
    def apply(s1: LKProof, s2: LKProof, term1oc: Occurrence, term2oc: Occurrence, trs: dbTRS) = {
      val (term1, term2) = getTerms(s1.root, s2.root, term1oc, term2oc, trs)
      val sequent = getSequent(s1.root, s2.root, term1, term2)

      new BinaryTree[Sequent](sequent, s1, s2)
        with BinaryLKProof with AuxiliaryFormulas {
        def rule = CutRuleType
        def aux = (term1::Nil)::(term2::Nil)::Nil
        override def name = "cut"
      }
    }
    def apply(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, trs: dbTRS) = {
      val (term1, term2) = getTerms(s1, s2, term1oc, term2oc, trs)
      getSequent(s1, s2, term1, term2)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, s2: LKProof, term: HOLFormula, trs: dbTRS): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas  = {
      val succ = s1.root.succedent.filter(x => unfoldSFormula(x.formula, trs) == unfoldSFormula(term, trs)).toList
      val ant = s2.root.antecedent.filter(x => unfoldSFormula(x.formula, trs) == unfoldSFormula(term, trs)).toList
  //    println("\n\nant = "+ant)
  //    println("succ = "+succ)
      (succ, ant) match {
        case ((x::_),(y::_)) => apply(s1, s2, x, y, trs)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1: Sequent, s2: Sequent, term1oc: Occurrence, term2oc: Occurrence, trs: dbTRS) = {
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
        if (unfoldSFormula(term1.formula, trs) != unfoldSFormula(term2.formula,trs)) throw new LKRuleCreationException("Formulas to be cut are not identical")
        else {
          (term1, term2)
        }
      }
    }
    private def getSequent(s1: Sequent, s2: Sequent, term1: Occurrence, term2: Occurrence) = {
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
      Some((r.uProof1, r.uProof2, r.root, a1, a2))
    }
    else None
  }



  object sContractionLeftRule {
    def apply(s1: LKProof, term1oc: Occurrence, term2oc: Occurrence, trs: dbTRS) = {
      val (term1, term2) = getTerms(s1.root, term1oc, term2oc, trs)
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
    def apply(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence, trs: dbTRS) = {
      val (term1, term2) = getTerms(s1, term1oc, term2oc, trs)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term1, term2, prinFormula)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, term1: HOLFormula, trs: dbTRS): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      (s1.root.antecedent.filter(x => unfoldSFormula(x.formula, trs) == unfoldSFormula(term1,trs))).toList match {
        case (x::y::_) => apply(s1, x, y, trs)
        case _ => throw new LKRuleCreationException("No matching formulas found to contract.")
      }
    }
    private def getTerms(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence, trs:dbTRS) = {
      val term1op = s1.antecedent.find(_ == term1oc)
      val term2op = s1.antecedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the left part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (unfoldSFormula(term1.formula, trs) != unfoldSFormula(term2.formula, trs)) throw new LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula.toStringSimple + ", term2.formula = " + term2.formula.toStringSimple)
        else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
        else {
          (term1, term2)
        }
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
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
      Some((r.uProof, r.root, a1, a2, p1))
    }
    else None
  }


  object sContractionRightRule {
    def apply(s1: LKProof, term1oc: Occurrence, term2oc: Occurrence, trs: dbTRS) = {
      val (term1, term2) = getTerms(s1.root, term1oc, term2oc, trs)
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
    def apply(s1: Sequent, term1oc: Occurrence, term2oc: Occurrence, trs: dbTRS) = {
      val (term1, term2) = getTerms(s1, term1oc, term2oc, trs)
      val prinFormula = getPrinFormula(term1, term2)
      getSequent(s1, term1, term2, prinFormula)
    }
    // convenient method to choose the first two formulas
    def apply(s1: LKProof, term1: HOLFormula, trs: dbTRS): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas  = {
      (s1.root.succedent.filter(x => unfoldSFormula(x.formula, trs) == unfoldSFormula(term1, trs))).toList match {
        case (x::y::_) => apply(s1, x, y, trs)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
    private def getTerms(s1 : Sequent, term1oc : Occurrence, term2oc : Occurrence, trs: dbTRS) = {
      val term1op = s1.succedent.find(_ == term1oc)
      val term2op = s1.succedent.find(_ == term2oc)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (unfoldSFormula(term1.formula, trs) != unfoldSFormula(term2.formula, trs)) throw new LKRuleCreationException("Formulas to be contracted are not identical: term1.formula = " + term1.formula.toStringSimple + ", term2.formula = " + term2.formula.toStringSimple)
        else if (term1 == term2) throw new LKRuleCreationException("Formulas to be contracted are of the same occurrence")
        else {
          (term1, term2)
        }
      }
    }
    private def getPrinFormula(term1: FormulaOccurrence, term2: FormulaOccurrence) = {
      val holterm1 = term1.formula.asInstanceOf[HOLFormula]
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
      Some((r.uProof, r.root, a1, a2, p1))
    }
    else None
  }


  //----------------------- trsArrowRule ------------------

  object trsArrowRule {
    def apply(s1: LKProof, auxf: FormulaOccurrence, trs: dbTRS) = {
      val prinFormula = factory.createFormulaOccurrence( unfoldSFormula(auxf.formula, trs), auxf  +: Seq.empty[FormulaOccurrence] )
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

    def apply(s1: LKProof, auxf: HOLFormula, trs: dbTRS): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.antecedent ++ s1.root.succedent).filter(x => unfoldSFormula(x.formula, trs) == unfoldSFormula(auxf, trs))).toList match {
        case (x::_) => apply(s1, x, trs)
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
    def apply(s1: LKProof, auxf: HOLFormula, trs: dbTRS): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      ((s1.root.succedent).filter(x => unfoldSFormula(x.formula, trs) == unfoldSFormula(auxf, trs))).toList match {
        case (x::_) => trsArrowRule.apply(s1, x, trs)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences in the right side found for application of the trsArrowRightRule with the given formula")
      }
    }
    def unapply(proof: LKProof) = if (proof.rule == trsArrowRightRule) {
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
    def apply(s1: LKProof, auxf: HOLFormula, trs: dbTRS): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
//      println("\n\ns1 = "+s1.root)
//      println("\n\nauxf = "+auxf)
      ((s1.root.antecedent).filter(x => unfoldSFormula(x.formula, trs) == unfoldSFormula(auxf, trs))).toList match {
        case (x::_) => trsArrowRule.apply(s1, x, trs)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences in the left side found for application of the trsArrowLeftRule with the given formula")
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
        // FIXME: cast needed???
        val sub = Substitution(ps.vars.zip(indices.asInstanceOf[List[HOLExpression]]))
     //   require( substitute(sub, ps.seq) == so.getSequent, "Proof Link to proof " + name + "(" + indices + ") with sequent " + so.getSequent + " incorrect!")

//        require( ps.seq.antecedent.map(fo => fo.formula).toSet == so.antecedent.map(fo => sub(fo.formula)).toSet)
//        require( ps.seq.succedent.map(fo => fo.formula).toSet == so.succedent.map(fo => sub(fo.formula)).toSet)
        require(ps.seq equals substitute(sub , so.toFSequent()) )

      }
    }
  }
