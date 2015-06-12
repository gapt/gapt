package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ Utils, FOLSubstitution }
import at.logic.gapt.grammars.SipGrammar
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.{ LKProof, FSequent }
import at.logic.gapt.provers.prover9.Prover9Prover

import scala.collection.mutable

/**
 * Models a simple induction proof.
 *
 * @param ExpSeq0 Instances for the induction base.
 * @param ExpSeq1 Instances for the induction step.
 * @param ExpSeq2 Instances for the conclusion.
 * @param t Terms used in the induction step.
 * @param u Terms used in the conclusion
 * @param inductionFormula The formula induced over. This argument defaults to X(α, ν, γ) with X a second-order variable, i.e. an unknown induction formula.
 */
class SimpleInductionProof( val ExpSeq0: ExpansionSequent,
                            val ExpSeq1: ExpansionSequent,
                            val ExpSeq2: ExpansionSequent,
                            val t: List[FOLTerm],
                            val u: List[FOLTerm],
                            val inductionFormula: HOLFormula = HOLAtom( Var( "X", Ti -> ( Ti -> ( Ti -> To ) ) ), FOLVar( "α" ), FOLVar( "ν" ), FOLVar( "γ" ) ) ) {
  import SimpleInductionProof._

  val p9prover = new Prover9Prover

  val Gamma0 = extractInstances( ExpSeq0 )
  val Gamma1 = extractInstances( ExpSeq1 )
  val Gamma2 = extractInstances( ExpSeq2 )

  require( freeVariables( Gamma0 ) subsetOf Set( alpha, beta ), "Gamma0 should contain only α, β, but freeVariables(Gamma0) = " + freeVariables( Gamma0 ).toString() )
  require( freeVariables( Gamma1 ) subsetOf Set( alpha, nu, gamma ), "Gamma1 should contain only α, ν, γ, but freeVariables(Gamma1) = " + freeVariables( Gamma1 ).toString() )
  require( freeVariables( Gamma2 ) subsetOf Set( alpha ), "Gamma2 should contain only α, but freeVariables(Gamma2) = " + freeVariables( Gamma2 ).toString() )

  require( freeVariables( u ) subsetOf Set( alpha ), "u should contain only α, but freeVariables(u) = " + freeVariables( u ) )
  require( freeVariables( t ) subsetOf Set( alpha, nu, gamma ), "t should contain only α, ν, γ, but freeVariables(t) = " + freeVariables( t ) )

  if ( inductionFormula != X ) {
    require( freeVariables( inductionFormula ) subsetOf Set( alpha, nu, gamma ), "F should contain only α, ν, γ, but freeVariables(F) = " + freeVariables( inductionFormula ) )
    require( inductionFormula.isInstanceOf[FOLFormula], "F is neither X(α, ν, γ) nor first order" )
  }

  private def F( x1: FOLTerm, x2: FOLTerm, x3: FOLTerm ): HOLFormula = {
    val sub = FOLSubstitution( List( alpha -> x1, nu -> x2, gamma -> x3 ) )
    sub( inductionFormula )
  }

  val Sequent0 = Gamma0 :+ F( alpha, zero, beta )

  val Ft = t map { F( alpha, nu, _ ) }
  val Sequent1 = Ft ++: Gamma1 :+ F( alpha, snu, gamma )

  val Fu = u map { F( alpha, alpha, _ ) }
  val Sequent2 = Fu ++: Gamma2

  var pi0Op: Option[LKProof] = None
  var pi1Op: Option[LKProof] = None
  var pi2Op: Option[LKProof] = None

  /**
   *
   * @return True if this is a schematic sip, i.e. the induction formula is unknown.
   */
  def isSchematic: Boolean = inductionFormula == X

  /**
   *
   * @return True if the induction formula is in fact a solution.
   */
  def isSolved: Boolean = p9prover.isValid( Sequent0 ) && p9prover.isValid( Sequent1 ) && p9prover.isValid( Sequent2 )

  /**
   * Uses prover9 to compute the subproofs π,,0,,, π,,1,,, π,,2,,, provided Sequent0, Sequent1, Sequent2 are provable.
   *
   */
  def subproofsFromProver9 = if ( isSolved ) {
    pi0Op = p9prover.getLKProof( Sequent0 )
    pi1Op = p9prover.getLKProof( Sequent1 )
    pi2Op = p9prover.getLKProof( Sequent2 )
  }

  /**
   * TODO: Find a better name for this
   *
   * @param f A FOLFormula
   * @return This with the induction formula replaced by f
   */
  def solve( f: FOLFormula ): SimpleInductionProof = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, f )

  /**
   * Converts this into an LKProof, if possible (i.e. inductionFormula is a solution).
   *
   * @return The LKProof represented by this object
   */
  def toLKProof: Option[LKProof] = {

    ( pi0Op, pi1Op, pi2Op ) match {
      case ( Some( pi0 ), Some( pi1 ), Some( pi2 ) ) =>
        // Induction base
        val inductionBase1 = proofFromInstances( pi0, ExpSeq0 )
        val inductionBase2 = CleanStructuralRules( ForallRightRule( inductionBase1, F( alpha, zero, beta ), All( y, F( alpha, zero, y ) ), beta ) )

        // Induction step
        val inductionStep1 = proofFromInstances( pi1, ExpSeq1 )
        val inductionStep2 = t.foldLeft( inductionStep1 ) {
          ( acc, ti ) => ForallLeftRule( acc, F( alpha, nu, ti ), All( y, F( alpha, nu, y ) ), ti )
        }
        val inductionStep3 = ForallRightRule( inductionStep2, F( alpha, snu, gamma ), All( y, F( alpha, snu, y ) ), gamma )

        val inductionStep4 = CleanStructuralRules( inductionStep3 )

        // Conclusion
        val conclusion1 = proofFromInstances( pi2, ExpSeq2 )
        val conclusion2 = u.foldLeft( conclusion1.asInstanceOf[LKProof] ) {
          ( acc: LKProof, ui ) => ForallLeftRule( acc, F( alpha, alpha, ui ), All( y, F( alpha, alpha, y ) ), ui )
        }
        val conclusion3 = CleanStructuralRules( conclusion2 )

        // Combining the proofs
        val inductionProof = InductionRule( inductionBase2,
          inductionStep4, All( y, F( alpha, zero, y ) ).asInstanceOf[FOLFormula],
          All( y, F( alpha, nu, y ) ).asInstanceOf[FOLFormula],
          All( y, F( alpha, snu, y ) ).asInstanceOf[FOLFormula],
          alpha )

        Some( CutRule( inductionProof, conclusion3, All( y, F( alpha, alpha, y ) ) ) )

      case _ if isSolved =>
        subproofsFromProver9; toLKProof
      case _ => None
    }

  }
}

object SimpleInductionProof {
  val y = FOLVar( "y" )
  val zero = FOLConst( "0" )
  val alpha = FOLVar( "α" )
  val beta = FOLVar( "β" )
  val gamma = FOLVar( "γ" )
  val nu = FOLVar( "ν" )
  val snu = FOLFunction( "s", List( nu ) )
  val X = HOLAtom( Var( "X", Ti -> ( Ti -> ( Ti -> To ) ) ), alpha, nu, gamma )

}

object decodeSipGrammar {
  import SipGrammar._

  def apply( encoding: InstanceTermEncoding, grammar: SipGrammar ) = {
    val seq0 = mutable.Buffer[FOLTerm]()
    val seq1 = mutable.Buffer[FOLTerm]()
    val seq2 = mutable.Buffer[FOLTerm]()
    val ts = mutable.Buffer[FOLTerm]()
    val us = mutable.Buffer[FOLTerm]()

    grammar.productions foreach {
      case ( `tau`, t ) =>
        val fvs = freeVariables( t )
        // FIXME: this produces many more instances than the paper, but seems necessary for isaplanner/prop_10
        if ( !fvs.contains( beta ) && !fvs.contains( gamma ) ) seq2 += FOLSubstitution( nu -> alpha )( t )
        if ( !fvs.contains( beta ) ) seq1 += t
        if ( !fvs.contains( gamma ) ) seq0 += FOLSubstitution( nu -> Utils.numeral( 0 ) )( t )
      case ( `gamma`, t )    => ts += t
      case ( `gammaEnd`, u ) => us += u
    }

    // dummy step terms
    if ( ts isEmpty ) ts += FOLConst( "0" )
    if ( us isEmpty ) us += FOLConst( "0" )

    new SimpleInductionProof( encoding.decodeToExpansionSequent( seq0 ),
      encoding.decodeToExpansionSequent( seq1 ),
      encoding.decodeToExpansionSequent( seq2 ),
      ts.toList, us.toList )
  }
}

object canonicalSolution {
  import SimpleInductionProof._

  def apply( sip: SimpleInductionProof, i: Int ): FOLFormula = i match {
    case 0 => FOLSubstitution( beta -> gamma )( sip.Gamma0.toNegFormula ).asInstanceOf[FOLFormula]
    case i =>
      val C_ = apply( sip, i - 1 )
      val nuSubst = FOLSubstitution( nu -> Utils.numeral( i - 1 ) )
      And( nuSubst( sip.Gamma1.toNegFormula ).asInstanceOf[FOLFormula],
        And( sip.t map { t => FOLSubstitution( gamma -> nuSubst( t ) )( C_ ) } ) )
  }
}