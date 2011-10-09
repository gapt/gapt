/*
 * robinson.scala
 *
 * Traditional resolution calculus with factors and para modulation. Using clauses
 */
package at.logic.calculi.resolution

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol.HOLFormula
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.acyclicGraphs._
import at.logic.language.lambda.substitutions._
import at.logic.calculi.lk.base._
import base._
import scala.collection.immutable.HashSet

package robinson {

import _root_.at.logic.language.fol.Neg
import _root_.at.logic.language.hol.{HOLVar, Formula, HOLExpression, Neg => HOLNeg}
import _root_.at.logic.language.lambda.substitutions.Substitution._
import _root_.at.logic.language.lambda.types.->
import _root_.at.logic.utils.traits.Occurrence
import collection.immutable.Seq
import at.logic.calculi.occurrences.FormulaOccurrence
trait CNF extends Sequent {require((antecedent++succedent).forall(x => x.formula match {case Atom(_,_) => true; case _ => false}))}

  object IsNeg {
    def apply(formula: HOLFormula) = formula match {
      case Neg(_) => true
      case _ => false
    }
  }
  object StripNeg {
    def apply(formula: HOLFormula) = formula match {
      case Neg(f) => f
      case _ => formula
    }
  }

  // the boolean represent isPositive as the negation is stripped from the literals
  class Clause(val literals: Seq[Pair[FormulaOccurrence,Boolean]]) extends Sequent(
    literals.filter(!_._2).map(_._1),
    literals.filter(_._2).map(_._1)
  ) with CNF {
    def negative = antecedent
    def positive = succedent
  }

  object Clause {
    def apply(literals: Seq[Pair[FormulaOccurrence,Boolean]]) = new Clause(literals)
    def apply(neg: Seq[FormulaOccurrence], pos: Seq[FormulaOccurrence]) = new Clause(neg.map((_,false)) ++ pos.map((_,true)))
    def unapply(s: Sequent) = s match {
      case c: Clause => Some(c.negative, c.positive)
      case _ => None
    }
  }

  object createContext {
    def apply(set: Seq[FormulaOccurrence], sub: Substitution[FOLExpression]): Seq[FormulaOccurrence] =
      set.map(x => x.factory.createFormulaOccurrence(sub(x.formula.asInstanceOf[FOLFormula]).asInstanceOf[HOLFormula], x::Nil))
  }

  case object VariantType extends UnaryRuleTypeA
  case object FactorType extends UnaryRuleTypeA
  case object ResolutionType extends BinaryRuleTypeA
  case object ParamodulationType extends BinaryRuleTypeA

  trait RobinsonResolutionProof extends ResolutionProof[Clause] {
    def getAccumulatedSubstitution: Substitution[FOLExpression]
  }

  object InitialClause {
    def apply(ant: Seq[FOLFormula], suc: Seq[FOLFormula]) (implicit factory: FOFactory): RobinsonResolutionProof = {
      val left: Seq[FormulaOccurrence] = ant.map(factory.createFormulaOccurrence(_,Nil))
      val right: Seq[FormulaOccurrence] = suc.map(factory.createFormulaOccurrence(_,Nil))
      new LeafAGraph[Clause](Clause(left, right)) with NullaryResolutionProof[Clause]  with RobinsonResolutionProof {
        def rule = InitialType
        override def name = ""
        def getAccumulatedSubstitution = Substitution[FOLExpression]()
      }
    }
    def apply(literals: Seq[FOLFormula]) (implicit factory: FOFactory): RobinsonResolutionProof = {
      val lits: Seq[Pair[FormulaOccurrence,Boolean]] = literals.map(l => if (IsNeg(l)) (factory.createFormulaOccurrence(StripNeg(l),Nil),false)
        else (factory.createFormulaOccurrence(l,Nil),true))
      new LeafAGraph[Clause](Clause(lits)) with NullaryResolutionProof[Clause] with RobinsonResolutionProof {
        def rule = InitialType
        override def name = ""
        def getAccumulatedSubstitution = Substitution[FOLExpression]()
      }
    }
    def unapply(proof: ResolutionProof[Clause]) = if (proof.rule == InitialType) Some((proof.root)) else None
  }

  // left side is always resolved on positive literal and right on negative
  object Resolution {
    def apply(p1: RobinsonResolutionProof, p2: RobinsonResolutionProof, a1: Occurrence, a2: Occurrence, sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val term1op = p1.root.succedent.find(_ == a1)
      val term2op = p2.root.antecedent.find(_ == a2)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (sub(term1.formula.asInstanceOf[FOLFormula]) != sub(term2.formula.asInstanceOf[FOLFormula])) throw new LKRuleCreationException("Formulas to be cut are not identical (modulo the given substitution)")
        else {
          new BinaryAGraph[Clause](Clause(
              createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent.filterNot(_ == term2), sub),
              createContext(p1.root.succedent.filterNot(_ == term1), sub) ++ createContext(p2.root.succedent, sub))
            , p1, p2)
            with BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
                def rule = ResolutionType
                def aux = (term1::Nil)::(term2::Nil)::Nil
                def substitution = sub
                override def toString = "Res(" + root.toString + ", " + p1.toString + ", " + p2.toString + ", " + substitution.toString + ")"
                override def name = "res"
                def getAccumulatedSubstitution = substitution compose p1.getAccumulatedSubstitution compose p2.getAccumulatedSubstitution
            }
        }
      }
    }
   def unapply(proof: ResolutionProof[Clause]) = if (proof.rule == ResolutionType) {
        val pr = proof.asInstanceOf[BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas]
        Some((pr.root, pr.uProof1.asInstanceOf[RobinsonResolutionProof], pr.uProof2.asInstanceOf[RobinsonResolutionProof], pr.aux.head.head, pr.aux.tail.head.head, pr.substitution))
      }
      else None
/*
    def apply(p1: ResolutionProof[Clause], p2: ResolutionProof[Clause], a1: FormulaOccurrence, a2: FormulaOccurrence ): ResolutionProof[Clause] = {
      val unifiers = FOLUnificationAlgorithm.unify( a1.formula.asInstanceOf[FOLExpression], a2.formula.asInstanceOf[FOLExpression] )
      if ( unifiers.isEmpty )
        throw new LKRuleCreationException("Auxiliary formulas " + a1.formula + " and " + a2.formula + " are not unifiable!")
      apply( p1, p2, a1, a2, unifiers.head.asInstanceOf[Substitution[FOLFormula]] )
    }
*/
  }

  object Paramodulation {
    def apply(p1: RobinsonResolutionProof, p2: RobinsonResolutionProof, a1: Occurrence, a2: Occurrence, newLiteral: FOLFormula, sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val term1op = p1.root.succedent.find(_ == a1)
      val term2opAnt = p2.root.antecedent.find(_ == a2)
      val term2opSuc = p2.root.succedent.find(_ == a2)
      if (term1op == None || (term2opAnt == None && term2opSuc == None)) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        if (term2opAnt != None) {
          val term2 = term2opAnt.get
          val prinFormula = term2.factory.createFormulaOccurrence(sub(newLiteral).asInstanceOf[FOLFormula], term1::term2::Nil)
          new BinaryAGraph[Clause](Clause(
              createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent.filterNot(_ == term2), sub) :+ prinFormula,
              createContext(p1.root.succedent.filterNot(_ == term1), sub) ++ createContext(p2.root.succedent, sub))
            , p1, p2)
            with BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
                def rule = ParamodulationType
                def aux = (term1::Nil)::(term2::Nil)::Nil
                def substitution = sub
                override def toString = "Para(" + root.toString + ", " + p1.toString + ", " + p2.toString + ", " + substitution.toString + ")"
                override def name = "pmod"
                def getAccumulatedSubstitution = substitution compose p1.getAccumulatedSubstitution compose p2.getAccumulatedSubstitution
            }
        }
        else {
          val term2 = term2opSuc.get
          val prinFormula = term2.factory.createFormulaOccurrence(sub(newLiteral).asInstanceOf[FOLFormula], term1::term2::Nil)
          new BinaryAGraph[Clause](Clause(
              createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent, sub),
              createContext(p1.root.succedent.filterNot(_ == term1), sub) ++ createContext(p2.root.succedent.filterNot(_ == term2), sub)  :+ prinFormula)
            , p1, p2)
            with BinaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
                def rule = ParamodulationType
                def aux = (term1::Nil)::(term2::Nil)::Nil
                def substitution = sub
                override def toString = "Para(" + root.toString + ", " + p1.toString + ", " + p2.toString + ", " + substitution.toString + ")"
                override def name = "pmod"
                def getAccumulatedSubstitution = substitution compose p1.getAccumulatedSubstitution compose p2.getAccumulatedSubstitution
            }
        }
      }
    }
  }


  object Variant {
    def apply(p: RobinsonResolutionProof, sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      require( sub.isRenaming )
      val newCl = Clause( createContext( p.root.antecedent, sub ), createContext( p.root.succedent, sub ) )
      new UnaryAGraph[Clause](newCl, p)
          with UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with RobinsonResolutionProof {
            def rule = VariantType
            def substitution = sub
            override def toString = "Vr(" + root.toString + ", " + p.toString + ", " + substitution.toString + ")"
            override def name = "variant"
            def getAccumulatedSubstitution = substitution compose p.getAccumulatedSubstitution
          }
    }

    def apply(p: RobinsonResolutionProof): ResolutionProof[Clause] = {
      // TODO: refactor the following into Sequent.getFreeAndBoundVariables
      val vars = (p.root.antecedent ++ p.root.succedent).foldLeft( HashSet[Var]() )( (m, f) => m ++ f.getFreeAndBoundVariables._1.asInstanceOf[Set[FOLVar]] )
      // TODO: should not be necessary to pass argument Ti() here.
      // we return an actual variant only if there are free variables, otherwise we return the parent proof as it does not change
      if (vars.isEmpty) p
      else apply( p, Substitution( vars.map( v => (v, v.factory.createVar( FreshVariableSymbolFactory.getVariableSymbol, Ti()) ) ).toMap ).asInstanceOf[Substitution[FOLExpression]] )
    }

    def unapply(proof: ResolutionProof[Clause] with AppliedSubstitution[FOLExpression]) = if (proof.rule == VariantType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression]]
        Some((pr.root, pr.uProof.asInstanceOf[RobinsonResolutionProof], pr.substitution))
      }
      else None
  }


  object Factor {
    // a factorization of both sides of the sequent
    def apply(p: RobinsonResolutionProof, a: Occurrence, oc1: Seq[Occurrence], b: Occurrence, oc2: Seq[Occurrence], sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val r = p.root.removeFormulasAtOccurrences(oc1 ++ oc2)
      val newCl = Clause( createContext( r.antecedent, sub ), createContext( r.succedent, sub ))
      new UnaryAGraph[Clause](newCl, p)
        with UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
          def rule = FactorType
          def substitution = sub
          def aux = (a.asInstanceOf[FormulaOccurrence]::b.asInstanceOf[FormulaOccurrence]::Nil)::Nil
          override def toString = "Fac(" + root + ", " + p.toString + ", " + substitution.toString + ")"
          override def name = "factor"
          def getAccumulatedSubstitution = substitution compose p.getAccumulatedSubstitution
        }
    }
    // the substitution contains also the substitutions generated by the resolution step happening later. We apply it now as it does not contain temporary substitutions for example:
    // we first resolve p(y), p(x), -p(f(y) with -p(a) to get p(y), -p(f(y)) with x -> a and then we look for possible factors, like y -> x and get the factor p(x), -p(f(x))
    // with substitution y -> x and x -> a. but as we combine the substitutions we cannot remove the substitution generated by the first step. This is not important as we apply
    // the same resolution step and therefore this substitution should be anyway generated.
    def apply(p: RobinsonResolutionProof, a: Occurrence, occurrencesToRemove: Seq[Occurrence], sub: Substitution[FOLExpression]): RobinsonResolutionProof = {
      val r = p.root.removeFormulasAtOccurrences(occurrencesToRemove)
      val newCl = Clause( createContext( r.antecedent, sub ), createContext( r.succedent, sub ))
      new UnaryAGraph[Clause](newCl, p)
        with UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas with RobinsonResolutionProof {
          def rule = FactorType
          def substitution = sub
          def aux = (a.asInstanceOf[FormulaOccurrence]::Nil)::Nil
          override def toString = "Fac(" + root + ", " + p.toString + ", " + substitution.toString + ")"
          override def name = "factor"
          def getAccumulatedSubstitution = substitution compose p.getAccumulatedSubstitution
        }
    }
    def unapply(proof: ResolutionProof[Clause] with AppliedSubstitution[FOLExpression]) = if (proof.rule == FactorType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution[FOLExpression] with AuxiliaryFormulas]
        Some((pr.root, pr.uProof.asInstanceOf[RobinsonResolutionProof], pr.aux.head, pr.substitution))
      }
      else None
  }

}
