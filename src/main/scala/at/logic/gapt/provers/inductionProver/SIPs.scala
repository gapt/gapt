package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ Utils, FOLSubstitution }
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.grammars.SipGrammar
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.proofs.resolution.{ ForgetfulParamodulate, MyFClause, ForgetfulResolve }
import at.logic.gapt.proofs.resolution.MyFClause._
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver
import at.logic.gapt.utils.logging.Logger

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

  /**
   *
   * @return True if this is a schematic sip, i.e. the induction formula is unknown.
   */
  def isSchematic: Boolean = inductionFormula == X

  /**
   *
   * @return True if the induction formula is in fact a solution.
   */
  def isSolved: Boolean = ( new VeriTProver ).isValid( Sequent0 ) && ( new VeriTProver ).isValid( Sequent1 ) && ( new VeriTProver ).isValid( Sequent2 )

  /**
   * TODO: Find a better name for this
   *
   * @param f A FOLFormula
   * @return This with the induction formula replaced by f
   */
  def solve( f: FOLFormula ): SimpleInductionProof = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, f )

  /**
   * Converts this into an LKProof, with user-supplied proofs π,,0,,, π,,1,,, π,,2,,.
   *
   * @param pi0 Proof of the induction base.
   * @param pi1 Proof of the induction step.
   * @param pi2 Proof of the conclusion.
   * @return The LKProof represented by this object.
   */
  def toLKProof( pi0: LKProof, pi1: LKProof, pi2: LKProof ): LKProof = {
    val indFormIsQuantified = freeVariables( inductionFormula ) contains gamma

    def Fprime( x1: FOLTerm, x2: FOLTerm ): FOLFormula =
      if ( indFormIsQuantified )
        All( y, F( x1, x2, y ) ).asInstanceOf[FOLFormula]
      else
        F( x1, x2, gamma ).asInstanceOf[FOLFormula]

    if ( indFormIsQuantified ) {
      require( t.nonEmpty, "Induction formula contains γ, but no step terms have been supplied." )
      require( u.nonEmpty, "Induction formula contains γ, but no cut terms have been supplied." )
    }

    // Induction base
    val inductionBase1 = proofFromInstances( pi0, ExpSeq0 )
    val inductionBase2 = ContractionMacroRule(
      if ( indFormIsQuantified )
        ForallRightRule( inductionBase1, F( alpha, zero, beta ), Fprime( alpha, zero ), beta )
      else
        inductionBase1 )

    // Induction step
    val inductionStep1 = proofFromInstances( pi1, ExpSeq1 )
    val inductionStep2 =
      if ( indFormIsQuantified ) {
        t.foldLeft( inductionStep1 ) {
          ( acc, ti ) => ForallLeftRule( acc, F( alpha, nu, ti ), All( y, F( alpha, nu, y ) ), ti )
        }
      } else
        inductionStep1

    val inductionStep3 = ContractionMacroRule(
      if ( indFormIsQuantified )
        ForallRightRule( inductionStep2, F( alpha, snu, gamma ), All( y, F( alpha, snu, y ) ), gamma )
      else
        inductionStep2 )

    // Conclusion
    val conclusion1 = proofFromInstances( pi2, ExpSeq2 )
    val conclusion2 = ContractionMacroRule(
      if ( indFormIsQuantified ) {
        u.foldLeft( conclusion1.asInstanceOf[LKProof] ) {
          ( acc: LKProof, ui ) => ForallLeftRule( acc, F( alpha, alpha, ui ), All( y, F( alpha, alpha, y ) ), ui )
        }
      } else
        conclusion1 )

    // Combining the proofs
    val inductionProof = ContractionMacroRule( InductionRule( inductionBase2,
      inductionStep3, Fprime( alpha, zero ).asInstanceOf[FOLFormula],
      Fprime( alpha, nu ).asInstanceOf[FOLFormula],
      Fprime( alpha, snu ).asInstanceOf[FOLFormula],
      alpha ) )

    CleanStructuralRules( ContractionMacroRule( CutRule( inductionProof, conclusion2, Fprime( alpha, alpha ) ) ) )
  }

  /**
   *
   * @param prover
   * @return
   */
  def toLKProof( prover: Prover ): LKProof = {

    val ( pi0Op, pi1Op, pi2Op ) = ( prover.getLKProof( Sequent0 ), prover.getLKProof( Sequent1 ), prover.getLKProof( Sequent2 ) )
    ( pi0Op, pi1Op, pi2Op ) match {
      case ( Some( pi0 ), Some( pi1 ), Some( pi2 ) ) => toLKProof( pi0, pi1, pi2 )
      case _                                         => throw new Exception( "Not a correct LKProof." )
    }
  }

  /**
   * Converts this into an LKProof, calling prover9 to provide π,,0,,, π,,1,,, π,,2,,.
   *
   * @return The LKProof represented by this object
   */
  def toLKProof: LKProof = toLKProof( new Prover9Prover )
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
        if ( sip.t.isEmpty )
          C_
        else
          And( sip.t map { t => FOLSubstitution( gamma -> nuSubst( t ) )( C_ ) } ) )
  }
}

object findConseq extends Logger {
  import SimpleInductionProof._

  val veriTProver = new VeriTProver()

  def apply( S: SimpleInductionProof, n: Int, A: List[MyFClause[FOLFormula]] ): Set[List[MyFClause[FOLFormula]]] = {
    debug( "findConseq called on A = " + A )
    val num = Utils.numeral( n )
    val Gamma2n = FOLSubstitution( alpha, num )( S.Gamma2 )
    var M = Set( A )

    ( ForgetfulResolve( A ) union ForgetfulParamodulate( A ) ).foreach { F: List[MyFClause[FOLFormula]] =>
      val Fui = S.u.map( ui => FOLSubstitution( List( alpha -> num, gamma -> ui ) )( CNFtoFormula( F ) ) )
      if ( veriTProver.isValid( Fui ++: Gamma2n ) )
        M = M union apply( S, n, F )
    }

    M
  }
}

object FindFormulaH {
  import SimpleInductionProof._

  val veriTProver = new VeriTProver()

  def apply( S: SimpleInductionProof, n: Int ): Option[( SimpleInductionProof, FOLFormula )] = {
    val num = Utils.numeral( n )
    val CSn = canonicalSolution( S, n )

    val M = findConseq( S, n, CNFp.toFClauseList( CSn ).map( toMyFClause ) ).toList.sortBy( _.length )

    val proofs = M.view.flatMap { F =>
      val C = CNFtoFormula( F )
      val pos = C.find( num ).toSet // If I understand the paper correctly, an improvement can be made here
      val posSets = pos.subsets().toList

      posSets.view.flatMap { P =>
        val Ctilde = ( C /: P )( ( acc, p ) => acc.replace( p, nu ).asInstanceOf[FOLFormula] )
        if ( S.solve( Ctilde ).isSolved )
          Some( ( S, Ctilde ) )
        else
          None
      }
    }

    proofs.headOption
  }
}