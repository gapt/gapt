/*
 * robinson.scala
 *
 * Traditional resolution calculus with factors and para modulation. Using clauses
 */
package at.logic.calculi.resolution

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
//import at.logic.language.hol._
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.acyclicGraphs._
import scala.collection.immutable._
import at.logic.language.lambda.substitutions._
import at.logic.calculi.lk.base._
import base._
//import at.logic.algorithms.unification.fol._

package robinson {

  trait CNF extends Sequent {require((antecedent++succedent).forall(x => x match {case Atom(_,_) => true; case _ => false}))}

  class Clause(neg: List[FOLFormula], pos: List[FOLFormula]) extends Sequent(neg, pos) with CNF {
    def negative = antecedent.asInstanceOf[List[FOLFormula]]
    def positive = succedent.asInstanceOf[List[FOLFormula]]
  }

  object Clause {
    def apply(neg: List[FOLFormula], pos: List[FOLFormula]) = new Clause(neg,pos)
    def unapply(s: Sequent) = s match {
      case c: Clause => Some(c.negative, c.positive)
      case _ => None
    }
  }

  class ClauseOccurrence(override val antecedent: Set[FormulaOccurrence], override val succedent: Set[FormulaOccurrence]) extends SequentOccurrence( antecedent, succedent )
  {
    def getClause = Clause( antecedent.toList.map( fo => fo.formula.asInstanceOf[FOLFormula] ), succedent.toList.map( fo => fo.formula.asInstanceOf[FOLFormula] ) )
//    def multisetEquals( o: SequentOccurrence ) = getSequent.multisetEquals(o.getSequent)
    //def multisetEquals( o: SequentOccurrence ) = (((antecedent.toList.map(x => x.formula)) == o.antecedent.toList.map(x => x.formula)) && ((succedent.toList.map(x => x.formula)) == o.succedent.toList.map(x => x.formula)))
    //override def toString : String = SequentFormatter.sequentOccurenceToString(this)
  }

  object ClauseOccurrence {
    def apply(antecedent: Set[FormulaOccurrence], succedent: Set[FormulaOccurrence]) = new ClauseOccurrence(antecedent, succedent)
    def unapply(so: ClauseOccurrence) = Some(so.antecedent, so.succedent)
  }

  object createContext {
    def apply(set: Set[FormulaOccurrence], sub: Substitution[FOLFormula]): Set[FormulaOccurrence] = 
      set.map(x => x.factory.createContextFormulaOccurrence(sub(x.formula.asInstanceOf[FOLFormula]), x, x::Nil, set - x))
    def apply(set: Set[FormulaOccurrence], binary: Set[FormulaOccurrence], sub: Substitution[FOLFormula]): Set[FormulaOccurrence] = 
      set.map(x => x.factory.createContextFormulaOccurrence(sub(x.formula.asInstanceOf[FOLFormula]), x, x::Nil, set - x, binary))
  }

  case object VariantType extends UnaryRuleTypeA
  case object FactorType extends UnaryRuleTypeA
  case object ResolutionType extends BinaryRuleTypeA

  object InitialClause {
    def apply(seq: Sequent)(implicit factory: FOFactory) = {
      val left: Set[FormulaOccurrence] = seq.antecedent.foldLeft(Set.empty[FormulaOccurrence])((st, form) => st + createOccurrence(form.asInstanceOf[FOLFormula], st, factory))
      val right: Set[FormulaOccurrence] = seq.succedent.foldLeft(Set.empty[FormulaOccurrence])((st, form) => st + createOccurrence(form.asInstanceOf[FOLFormula], st, factory))
      new LeafAGraph[ClauseOccurrence](ClauseOccurrence(left, right)) with NullaryResolutionProof[ClauseOccurrence] {def rule = InitialType}
    }

    def createOccurrence(f: FOLFormula, others: Set[FormulaOccurrence], factory: FOFactory): FormulaOccurrence = factory.createPrincipalFormulaOccurrence(f, Nil, others)

    def unapply(proof: ResolutionProof[ClauseOccurrence]) = if (proof.rule == InitialType) Some((proof.root)) else None
  }

  // left side is always resolved on positive literal and right on negative
  object Resolution {
    def apply(p1: ResolutionProof[ClauseOccurrence], p2: ResolutionProof[ClauseOccurrence], a1: FormulaOccurrence, a2: FormulaOccurrence, sub: Substitution[FOLFormula]): ResolutionProof[ClauseOccurrence] = {
      val term1op = p1.root.succedent.find(x => x == a1)
      val term2op = p2.root.antecedent.find(x => x == a2)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        if (sub(term1.formula.asInstanceOf[FOLFormula]) != sub(term2.formula.asInstanceOf[FOLFormula])) throw new LKRuleCreationException("Formulas to be cut are not identical (modulo the given substitution)")
        else {
          new BinaryAGraph[ClauseOccurrence](ClauseOccurrence(
              createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent - term2, p1.root.antecedent, sub),
              createContext(p1.root.succedent - term1, sub) ++ createContext(p2.root.succedent, p1.root.succedent - term1, sub))
            , p1, p2)
            with BinaryResolutionProof[ClauseOccurrence] with AppliedSubstitution[FOLFormula] with AuxiliaryFormulas {
                def rule = ResolutionType
                def aux = (term1::Nil)::(term2::Nil)::Nil
                def substitution = sub
            }
        }
      }
    }
/*
    def apply(p1: ResolutionProof[ClauseOccurrence], p2: ResolutionProof[ClauseOccurrence], a1: FormulaOccurrence, a2: FormulaOccurrence ): ResolutionProof[ClauseOccurrence] = {
      val unifiers = FOLUnificationAlgorithm.unify( a1.formula.asInstanceOf[FOLExpression], a2.formula.asInstanceOf[FOLExpression] )
      if ( unifiers.isEmpty )
        throw new LKRuleCreationException("Auxiliary formulas " + a1.formula + " and " + a2.formula + " are not unifiable!")
      apply( p1, p2, a1, a2, unifiers.head.asInstanceOf[Substitution[FOLFormula]] )
    }
*/
  }
/*
  // TODO: here we need information on where to put the newLiteral
  object Paramodulation {
    def apply(p1: ResolutionProof[ClauseOccurrence], p2: ResolutionProof[ClauseOccurrence], a1: FormulaOccurrence, a2: FormulaOccurrence, newLiteral: FOLFormula, sub: Substitution[FOLFormula]): ResolutionProof[ClauseOccurrence] = {
      val term1op = p1.root.succedent.find(x => x == a1)
      val term2op = p2.root.antecedent.find(x => x == a2)
      if (term1op == None || term2op == None) throw new LKRuleCreationException("Auxialiary formulas are not contained in the right part of the sequent")
      else {
        val term1 = term1op.get
        val term2 = term2op.get
        val prinFormula = term1.factory.createPrincipalFormulaOccurrence(newLiteral, term1::term2::Nil, ((s1.root.succedent - term1) ++ (s2.root.succedent - term2)))
        new BinaryAGraph[ClauseOccurrence](ClauseOccurrence(
            createContext(p1.root.antecedent, sub) ++ createContext(p2.root.antecedent - term2, p1.root.antecedent, sub),
            createContext(p1.root.succedent - term1, sub) ++ createContext(p2.root.succedent, p1.root.succedent - term1, sub))
          , p1, p2)
          with BinaryResolutionProof[ClauseOccurrence] with AppliedSubstitution[FOLFormula] with AuxiliaryFormulas {
              def rule = ResolutionType
              def aux = (term1::Nil)::(term2::Nil)::Nil
              def substitution = sub
          }
      }
    }
  }
*/

  object Variant {
    def apply(p: ResolutionProof[ClauseOccurrence], sub: Substitution[FOLFormula]): ResolutionProof[ClauseOccurrence] = {
      require( sub.isRenaming )
      val newCl = ClauseOccurrence( createContext( p.root.antecedent, sub ), createContext( p.root.succedent, sub ) )
      new UnaryAGraph[ClauseOccurrence](newCl, p)
          with UnaryResolutionProof[ClauseOccurrence] with AppliedSubstitution[FOLFormula] {def rule = VariantType; def substitution = sub}
    }

    /* TODO: does not compile!
    def apply(p: ResolutionProof[ClauseOccurrence]): ResolutionProof[ClauseOccurrence] = {
      // TODO: refactor the following into Sequent.getFreeAndBoundVariables
      val vars = (p.root.getSequent.antecedent ++ p.root.getSequent.succedent).foldLeft( HashSet[FOLVar]() )( (m, f) => m ++ f.getFreeAndBoundVariables._1.asInstanceOf[Set[FOLVar]] )
      apply( p, Substitution( vars.map( v => (v, fol.createVar( FreshVariableSymbolFactory.getVariableSymbol) ) ).toMap ) )
    }
    */

    def unapply(proof: ResolutionProof[ClauseOccurrence] with AppliedSubstitution[FOLFormula]) = if (proof.rule == VariantType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[ClauseOccurrence] with AppliedSubstitution[FOLFormula]]
        Some((pr.root, pr.uProof, pr.substitution))
      }
      else None
  }
/*
  // the substitution contains also the substitutions generated by the resolution step happening later. We apply it now as it does not contain temporary substitutions for example:
  // we first resolve p(y), p(x), -p(f(y) with -p(a) to get p(y), -p(f(y)) with x -> a and then we look for possible factors, like y -> x and get the factor p(x), -p(f(x))
  // with substitution y -> x and x -> a. but as we combine the substitutions we cannot remove the substitution generated by the first step. This is not important as we apply
  // the same resolution step and therefore this substitution should be anyway generated.
  object Factor {
    def apply[T <: LambdaExpression](p: ResolutionProof[Clause], indicesToRemove: List[Int], sub: Substitution[T]): ResolutionProof[Clause] = {
      new UnaryAGraph[Clause]({val r = p.root.removeFormulasAtIndices(indicesToRemove); Clause(r.negative.map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]), r.positive.map(x => sub(x.asInstanceOf[T]).asInstanceOf[HOLFormula]))}, p)
        with UnaryResolutionProof[Clause] with AppliedSubstitution[T] {def rule = FactorType; def substitution = sub}
    }
    def unapply[T <: LambdaExpression](proof: ResolutionProof[Clause] with AppliedSubstitution[T]) = if (proof.rule == FactorType) {
        val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution[T]]
        Some((pr.root, pr.uProof, pr.substitution))
      }
      else None
  }
*/
}
