package at.logic.calculi.lk

import at.logic.algorithms.matching.FOLMatchingAlgorithm
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.proofs.{ BinaryRuleTypeA, RuleTypeA }
import at.logic.language.fol._
import at.logic.language.hol.HOLConst
import at.logic.utils.ds.acyclicGraphs.AGraph
import at.logic.utils.ds.trees.{ BinaryTree, LeafTree }

case object InductionRuleType extends BinaryRuleTypeA

object InductionRule {
  def apply( s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, term3oc: FormulaOccurrence ) = {

    val ( occZero, occX, occSx ) = getTerms( s1, s2, term1oc, term2oc, term3oc )
    val ( aZero, aX, aSx ) = ( occZero.formula.asInstanceOf[FOLFormula], occX.formula.asInstanceOf[FOLFormula], occSx.formula.asInstanceOf[FOLFormula] )

    // Find a substitution for A[x] and A[0], if possible.
    val sub1 = FOLMatchingAlgorithm.matchTerms( aX, aZero ) match {
      case Some( s ) => s

      case None      => throw new LKRuleCreationException( "Formula " + aX + " can't be matched to formula " + aZero + "." )
    }

    // Find a substitution for A[x] and A[Sx], if possible.
    val sub2 = FOLMatchingAlgorithm.matchTerms( aX, aSx ) match {
      case Some( s ) => s

      case None      => throw new LKRuleCreationException( "Formula " + aX + " can't be matched to formula " + aSx + "." )
    }

    // Some safety checks
    if ( sub1.domain.length != 1 )
      throw new LKRuleCreationException( "Formula " + aX + " can't be matched to formula " + aZero + " by substituting a single variable." )

    if ( sub2.domain.length != 1 )
      throw new LKRuleCreationException( "Formula " + aX + " can't be matched to formula " + aSx + " by substituting a single variable." )

    if ( sub1.domain != sub2.domain )
      throw new LKRuleCreationException( "Formula " + aX + " can't be matched to formulas " + aZero + " and " + aSx + " by substituting a single variable." )

    val x = sub1.domain.head.asInstanceOf[FOLVar]
    val zero = FOLConst( "0" )
    val sX = Function( "S", List( x ) )

    if ( sub1 != Substitution( x, zero ) )
      throw new LKRuleCreationException( sub1 + " doesn't replace " + x + " by 0." )

    if ( sub2 != Substitution( x, sX ) )
      throw new LKRuleCreationException( sub2 + " doesn't replace " + x + " by " + sX + "." )

    // Test the eigenvariable condition
    if ( ( s2.root.antecedent.filterNot( _ == occX ) ++ s2.root.succedent.filterNot( _ == occSx ) ) map ( _.formula.asInstanceOf[FOLFormula] ) flatMap freeVariables.apply contains x )
      throw new LKRuleCreationException( "Eigenvariable condition not satisified for sequent " + s2.root + " and variable " + x + "." )

    // Construct the primary formula occurrence
    val prinOcc = occX.factory.createFormulaOccurrence( aX, List( occZero, occX, occSx ) )

    // Construct the new sequent
    val ant = createContext( s1.root.antecedent ++ s2.root.antecedent.filterNot( _ == occX ) )
    val suc = createContext( s1.root.succedent.filterNot( _ == occZero ) ++ s2.root.succedent.filterNot( _ == occSx ) )
    val newSeq = Sequent( ant, prinOcc +: suc )

    // Construct the new proof
    new BinaryTree[Sequent]( newSeq, s1, s2 ) with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas {
      def rule = InductionRuleType

      def aux = List( occZero ) :: List( occX, occSx ) :: Nil
      def prin = List( prinOcc )
      override def name = "ind"
    }
  }

  def apply( s1: LKProof, s2: LKProof, inductionBase: FOLFormula, inductionHypo: FOLFormula, inductionStep: FOLFormula ): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    val term1oc = s1.root.succedent find ( _.formula == inductionBase ) match {
      case None      => throw new LKRuleCreationException( "Formula " + inductionBase + " not found in " + s1.root.succedent + "." )
      case Some( o ) => o
    }

    val term2oc = s2.root.antecedent find ( _.formula == inductionHypo ) match {
      case None      => throw new LKRuleCreationException( "Formula " + inductionHypo + " not found in " + s2.root.antecedent + "." )
      case Some( o ) => o
    }

    val term3oc = s2.root.succedent find ( _.formula == inductionStep ) match {
      case None      => throw new LKRuleCreationException( "Formula " + inductionStep + " not found in " + s2.root.succedent + "." )
      case Some( o ) => o
    }

    apply( s1, s2, term1oc, term2oc, term3oc )
  }

  def unapply( proof: LKProof ) = {
    if ( proof.rule == InductionRuleType ) {
      val r = proof.asInstanceOf[BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas]
      val ( ( base :: Nil ) :: ( step1 :: step2 :: Nil ) :: Nil ) = r.aux
      val ( p1 :: Nil ) = r.prin
      Some( ( r.uProof1, r.uProof2, r.root, base, step1, step2, p1 ) )
    } else None
  }

  private def getTerms( s1: LKProof, s2: LKProof, occ1: FormulaOccurrence, occ2: FormulaOccurrence, occ3: FormulaOccurrence ): ( FormulaOccurrence, FormulaOccurrence, FormulaOccurrence ) = {
    val occZero = s1.root.succedent.find( _ == occ1 ) match {
      case None      => throw new LKRuleCreationException( "Occurrence " + occ1 + " could not be found in " + s1.root.succedent + "." )
      case Some( o ) => o
    }

    val occX = s2.root.antecedent.find( _ == occ2 ) match {
      case None      => throw new LKRuleCreationException( "Occurrence " + occ2 + " could not be found in " + s2.root.antecedent + "." )
      case Some( o ) => o
    }

    val occSx = s2.root.succedent.find( _ == occ3 ) match {
      case None      => throw new LKRuleCreationException( "Occurrence " + occ3 + " could not be found in " + s2.root.succedent + "." )
      case Some( o ) => o
    }

    ( occZero, occX, occSx )
  }

}