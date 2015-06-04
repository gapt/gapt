package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._
import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.proofs.BinaryRuleTypeA
import at.logic.gapt.utils.ds.trees.BinaryTree

case object InductionRuleType extends BinaryRuleTypeA

/**
 * Binary induction rule:
 *
 * Γ |- Δ, A[0]        A[x], Π |- Λ, A[S(x)]
 * -----------------------------------------
 *          Γ, Π |- Δ, Λ, A[x]
 *
 */
object InductionRule {

  private val zero = FOLConst( "0" )
  private def S( t: FOLTerm ) = FOLFunction( "S", List( t ) )

  /**
   * Constructs a proof ending with an induction rule.
   *
   * @param s1 The left subproof. The succedent of its end sequent has to contain A[0].
   * @param s2 The right subproof. Its end sequent must contain A[x] in the antecedent and A[S(x)] in the succedent.
   * @param term1oc The occurrence of A[0] in the succedent of s1.
   * @param term2oc The occurrence of A[x] in the antecedent of s2.
   * @param term3oc The occurrence of A[S(x)] in the succedent of s2.
   * @return A proof ending with an induction rule. Its main formula will be A[x].
   */
  def apply( s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, term3oc: FormulaOccurrence ) = {

    val ( occZero, occX, occSx ) = getTerms( s1, s2, term1oc, term2oc, term3oc )
    val ( aZero, aX, aSx ) = ( occZero.formula.asInstanceOf[FOLFormula], occX.formula.asInstanceOf[FOLFormula], occSx.formula.asInstanceOf[FOLFormula] )

    // Find a FOLSubstitution for A[x] and A[0], if possible.
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
    val sX = S( x )

    if ( sub1 != FOLSubstitution( x, zero ) )
      throw new LKRuleCreationException( sub1 + " doesn't replace " + x + " by 0." )

    if ( sub2 != FOLSubstitution( x, sX ) )
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

  /**
   * Convenience constructor that finds appropriate formula occurrences on its own.
   */
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

  /**
   * Convenience constructor that attempts to find auxiliary formulas on its own.
   *
   * Given a proposed main formula A, it will try to find a variable x such that A[x\0], A[x], A[x\S(x)] are contained in the correct parts of s1 and s2.
   *
   */
  def apply( s1: LKProof, s2: LKProof, main: FOLFormula ): BinaryTree[Sequent] with BinaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    val inductionHypoOc = s2.root.antecedent find ( _.formula == main ) match {
      case Some( fo ) => fo
      case None       => throw new LKRuleCreationException( "Proposed main formula" + main + " not found in " + s2.root.antecedent + "." )
    }

    val inductionHypo = inductionHypoOc.formula.asInstanceOf[FOLFormula]

    val inductionBaseOc = s1.root.succedent find (
      fo => FOLMatchingAlgorithm.matchTerms( inductionHypo, fo.formula.asInstanceOf[FOLFormula] ) match {
        case Some( sub ) =>
          if ( sub.domain.length == 1 ) {
            val v = sub.domain.head.asInstanceOf[FOLVar]
            sub.map( v ) == zero
          } else
            false
        case None => false
      } ) match {
        case Some( fo ) => fo
        case None       => throw new LKRuleCreationException( "No suitable induction base formula found in " + s1.root.succedent )
      }

    val inductionStepOc = s2.root.succedent find (
      fo => FOLMatchingAlgorithm.matchTerms( inductionHypo, fo.formula.asInstanceOf[FOLFormula] ) match {
        case Some( sub ) =>
          if ( sub.domain.length == 1 ) {
            val v = sub.domain.head.asInstanceOf[FOLVar]
            sub.map( v ) == S( v )
          } else
            false
        case None => false
      } ) match {
        case Some( fo ) => fo
        case None       => throw new LKRuleCreationException( "Now suitable induction step formula found in " + s2.root.succedent )
      }

    apply( s1, s2, inductionBaseOc, inductionHypoOc, inductionStepOc )
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
