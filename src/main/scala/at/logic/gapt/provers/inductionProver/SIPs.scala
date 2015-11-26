package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ Utils, FOLSubstitution }
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.grammars.SipGrammar
import at.logic.gapt.proofs.FOLClause
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.resolution.{ forgetfulPropResolve, forgetfulPropParam }
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.veriT.VeriT
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
class SimpleInductionProof(
    val ExpSeq0:          ExpansionSequent,
    val ExpSeq1:          ExpansionSequent,
    val ExpSeq2:          ExpansionSequent,
    val t:                List[FOLTerm],
    val u:                List[FOLTerm],
    val inductionFormula: HOLFormula       = HOLAtom( Var( "X", Ti -> ( Ti -> ( Ti -> To ) ) ), FOLVar( "α" ), FOLVar( "ν" ), FOLVar( "γ" ) )
) {
  import SimpleInductionProof._

  val Gamma0 = extractInstances( ExpSeq0 )
  val Gamma1 = extractInstances( ExpSeq1 )
  val Gamma2 = extractInstances( ExpSeq2 )

  val EndSequent = ( toShallow( ExpSeq0 ) ++ toShallow( ExpSeq1 ) ++ toShallow( ExpSeq2 ) ).distinct

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

  private def Fprime( x1: FOLTerm, x2: FOLTerm ): FOLFormula =
    if ( indFormIsQuantified )
      All( y, F( x1, x2, y ) ).asInstanceOf[FOLFormula]
    else
      F( x1, x2, gamma ).asInstanceOf[FOLFormula]

  val Sequent0 = Gamma0 :+ F( alpha, zero, beta )

  val Ft = if ( t.isEmpty )
    List( F( alpha, nu, gamma ) )
  else
    t map { F( alpha, nu, _ ) }
  val Sequent1 = Ft ++: Gamma1 :+ F( alpha, snu, gamma )

  val Fu = if ( u.isEmpty )
    List( F( alpha, alpha, gamma ) )
  else
    u map { F( alpha, alpha, _ ) }
  val Sequent2 = Fu ++: Gamma2

  /**
   * Returns true iff the induction formula needs to be quantified over.
   *
   * @return
   */
  def indFormIsQuantified = freeVariables( inductionFormula ) contains gamma

  /**
   *
   * @return True if this is a schematic sip, i.e. the induction formula is unknown.
   */
  def isSchematic: Boolean = inductionFormula == X

  /**
   *
   * @return True if the induction formula is in fact a solution.
   */
  def isSolved( prover: Prover ): Boolean = prover.isValid( Sequent0 ) && prover.isValid( Sequent1 ) && prover.isValid( Sequent2 )
  def isSolved: Boolean = isSolved( VeriT )

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
    if ( indFormIsQuantified ) {
      require( t.nonEmpty, "Induction formula contains γ, but no step terms have been supplied." )
      require( u.nonEmpty, "Induction formula contains γ, but no cut terms have been supplied." )
    }

    // Induction base
    val inductionBase1 = proofFromInstances( pi0, ExpSeq0 )
    val inductionBase2 = ContractionMacroRule(
      if ( indFormIsQuantified )
        ForallRightRule( inductionBase1, Fprime( alpha, zero ), beta )
      else
        inductionBase1
    )

    // Induction step
    val inductionStep1 = proofFromInstances( pi1, ExpSeq1 )
    val inductionStep2 =
      if ( indFormIsQuantified ) {
        t.foldLeft( inductionStep1 ) {
          ( acc, ti ) => ForallLeftRule( acc, All( y, F( alpha, nu, y ) ), ti )
        }
      } else
        inductionStep1

    val inductionStep3 = ContractionMacroRule(
      if ( indFormIsQuantified )
        ForallRightRule( inductionStep2, All( y, F( alpha, snu, y ) ), gamma )
      else
        inductionStep2
    )

    // Conclusion
    val conclusion1 = proofFromInstances( pi2, ExpSeq2 )
    val conclusion2 = ContractionMacroRule(
      if ( indFormIsQuantified ) {
        u.foldLeft( conclusion1.asInstanceOf[LKProof] ) {
          ( acc: LKProof, ui ) => ForallLeftRule( acc, All( y, F( alpha, alpha, y ) ), ui )
        }
      } else
        conclusion1
    )
    val x = FOLVar( "x" )
    val conclusion3 = ForallLeftRule( conclusion2, All( x, Fprime( alpha, x ) ), alpha )

    // Combining the proofs
    val inductionProof = ContractionMacroRule( NaturalNumberInductionRule(
      inductionBase2,
      Fprime( alpha, zero ),
      inductionStep3,
      Fprime( alpha, nu ),
      Fprime( alpha, snu ),
      All( x, Fprime( alpha, x ) )
    ) )

    cleanStructuralRules( ContractionMacroRule( CutRule( inductionProof, conclusion3, All( x, Fprime( alpha, x ) ) ) ) )
  }

  /**
   *
   * @param prover The prover used to generate π,,0,, ,…,π,,2,,.
   * @return
   */
  def toLKProof( prover: Prover ): LKProof = {

    val ( pi0Op, pi1Op, pi2Op ) = ( prover.getLKProof( Sequent0 ), prover.getLKProof( Sequent1 ), prover.getLKProof( Sequent2 ) )
    ( pi0Op, pi1Op, pi2Op ) match {
      case ( Some( pi0 ), Some( pi1 ), Some( pi2 ) ) => toLKProof( cleanStructuralRules( pi0 ), cleanStructuralRules( pi1 ), cleanStructuralRules( pi2 ) )
      case _                                         => throw new Exception( "Not a correct LKProof." )
    }
  }

  /**
   * Converts this into an LKProof, calling prover9 to provide π,,0,,, π,,1,,, π,,2,,.
   *
   * @return The LKProof represented by this object
   */
  def toLKProof: LKProof = toLKProof( Prover9 )

  /**
   * Computes the nth instance proof. Uses prover9 to compute the subproofs.
   *
   * @param n A natural number
   * @return The nth instance of this sip.
   */
  def toInstanceLKProof( n: Int, rename: Boolean ): LKProof = toInstanceLKProof( n, Prover9, rename )

  /**
   * Computes the nth instance proof,
   *
   * @param n A natural number
   * @param prover The prover used to generate π,,0,, ,…,π,,2,,.
   * @return The nth instance of this sip.
   */
  def toInstanceLKProof( n: Int, prover: Prover, rename: Boolean ): LKProof = {

    val ( pi0Op, pi1Op, pi2Op ) = ( prover.getLKProof( Sequent0 ), prover.getLKProof( Sequent1 ), prover.getLKProof( Sequent2 ) )
    ( pi0Op, pi1Op, pi2Op ) match {
      case ( Some( pi0 ), Some( pi1 ), Some( pi2 ) ) => toInstanceLKProof( n, cleanStructuralRules( pi0 ), cleanStructuralRules( pi1 ), cleanStructuralRules( pi2 ), rename )
      case _                                         => throw new Exception( "Not a correct LKProof." )
    }
  }

  /**
   * Computes the nth instance proof, with user-supplied proofs π,,0,,, π,,1,,, π,,2,,.
   *
   * @param n A natural number
   * @param pi0 Proof of the induction base.
   * @param pi1 Proof of the induction step.
   * @param pi2 Proof of the conclusion.
   * @return The nth instance of this sip.
   */
  def toInstanceLKProof( n: Int, pi0: LKProof, pi1: LKProof, pi2: LKProof, rename: Boolean ): LKProof = {
    def num( k: Int ) = Utils.numeral( k )
    def gam( k: Int ) = FOLVar( "γ_" + k )

    val baseSub = if ( rename )
      FOLSubstitution( List( alpha -> num( n ), beta -> gam( 0 ) ) )
    else
      FOLSubstitution( alpha, num( n ) )

    val inductionBase1 = applySubstitution( baseSub )( proofFromInstances( pi0, ExpSeq0 ) )
    val inductionBase = ContractionMacroRule(
      if ( indFormIsQuantified )
        ForallRightRule( inductionBase1, baseSub( Fprime( alpha, zero ) ), baseSub( beta ).asInstanceOf[FOLVar] )
      else
        inductionBase1
    )

    def inductionStep( k: Int ) = {
      val sub =
        if ( rename )
          FOLSubstitution( List( alpha -> num( n ), nu -> num( k ), gamma -> gam( k + 1 ) ) )
        else
          FOLSubstitution( List( alpha -> num( n ), nu -> num( k ) ) )

      val inductionStep1 = applySubstitution( sub )( proofFromInstances( pi1, ExpSeq1 ) )
      val inductionStep2 =
        if ( indFormIsQuantified ) {
          t.foldLeft( inductionStep1 ) {
            ( acc, ti ) => ForallLeftRule( acc, sub( All( y, F( alpha, nu, y ) ) ), sub( ti ) )
          }
        } else
          inductionStep1

      ContractionMacroRule(
        if ( indFormIsQuantified )
          ForallRightRule( inductionStep2, sub( All( y, F( alpha, snu, y ) ) ), sub( gamma ).asInstanceOf[FOLVar] )
        else
          inductionStep2
      )
    }

    val stepsProof = ( inductionBase /: ( 0 until n ) ) { ( acc, i ) =>
      CutRule( acc, inductionStep( i ), Fprime( num( n ), num( i ) ) )
    }

    val conclusionSub = FOLSubstitution( alpha, num( n ) )

    val conclusion1 = proofFromInstances( pi2, ExpSeq2 )
    val conclusion2 = ContractionMacroRule(
      if ( indFormIsQuantified ) {
        u.foldLeft( conclusion1.asInstanceOf[LKProof] ) {
          ( acc: LKProof, ui ) => ForallLeftRule( acc, All( y, F( alpha, alpha, y ) ), ui )
        }
      } else
        conclusion1
    )

    val conclusion = applySubstitution( conclusionSub )( conclusion2 )

    CutRule( stepsProof, conclusion, Fprime( num( n ), num( n ) ) )
  }

  /**
   * Extracts a SIP grammar from the SIP according to the paper.
   *
   * @return The grammar corresponding to the sip.
   */
  def toSipGrammar: SipGrammar = {
    import SipGrammar._

    val termEncoding = FOLInstanceTermEncoding( EndSequent )
    val terms = termEncoding.encode( ExpSeq0 ) ++ termEncoding.encode( ExpSeq1 ) ++ termEncoding.encode( ExpSeq2 ) map { _.asInstanceOf[FOLTerm] }
    val tauProductions = terms map { x => tau -> x }
    val gammaProductions = t map { ti => gamma -> ti }
    val gammaEndProductions = u map { ui => gammaEnd -> ui }

    SipGrammar( tauProductions ++ gammaProductions ++ gammaEndProductions )
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

    new SimpleInductionProof(
      encoding.decodeToExpansionSequent( seq0 ),
      encoding.decodeToExpansionSequent( seq1 ),
      encoding.decodeToExpansionSequent( seq2 ),
      ts.toList, us.toList
    )
  }
}

object canonicalSolution {
  import SimpleInductionProof._

  def apply( sip: SimpleInductionProof, i: Int ): FOLFormula = i match {
    case 0 => FOLSubstitution( beta -> gamma )( sip.Gamma0.toNegFormula ).asInstanceOf[FOLFormula]
    case _ =>
      val C_ = apply( sip, i - 1 )
      val nuSubst = FOLSubstitution( nu -> Utils.numeral( i - 1 ) )
      And(
        nuSubst( sip.Gamma1.toNegFormula ).asInstanceOf[FOLFormula],
        if ( sip.t.isEmpty )
          C_
        else
          And( sip.t map { t => FOLSubstitution( gamma -> nuSubst( t ) )( C_ ) } )
      )
  }
}

object findConseq extends Logger {
  import SimpleInductionProof._
  type CNF = Set[FOLClause]

  def apply( S: SimpleInductionProof, n: Int, A: CNF, M: Set[CNF], forgetClauses: Boolean, prover: Prover ): Set[CNF] = {
    val num = Utils.numeral( n )
    val Gamma2n = FOLSubstitution( alpha, num )( S.Gamma2 )

    val newCNFs = if ( forgetClauses )
      forgetfulPropResolve( A ) union forgetfulPropParam( A ) union ForgetOne( A )
    else
      forgetfulPropResolve( A ) union forgetfulPropParam( A )

    ( ( M + A ) /: newCNFs ) { ( acc: Set[CNF], F: CNF ) =>
      if ( acc contains F ) {
        acc
      } else {
        val Fu = S.u.map( ui => FOLSubstitution( alpha, num )( FOLSubstitution( gamma, ui )( And( F map { _.toFormula } ) ) ) )
        if ( prover.isValid( Fu ++: Gamma2n ) )
          apply( S, n, F, acc, forgetClauses, prover )
        else
          acc
      }
    }
  }

  def apply( S: SimpleInductionProof, n: Int, A: FOLFormula, M: Set[CNF], forgetClauses: Boolean = false, prover: Prover = VeriT ): Set[CNF] =
    apply( S, n, CNFp.toClauseList( A ).map { _.distinct.sortBy { _.hashCode } }.toSet, M, forgetClauses, prover )

  def ForgetOne( A: CNF ) = for ( a <- A ) yield A - a
}

object FindFormulaH extends Logger {
  import SimpleInductionProof._

  def apply( S: SimpleInductionProof, n: Int, forgetClauses: Boolean = false, prover: Prover = VeriT ): Option[FOLFormula] = {
    val CSn = canonicalSolution( S, n )
    apply( CSn, S, n, forgetClauses, prover )
  }

  def apply( CSn: FOLFormula, S: SimpleInductionProof, n: Int, forgetClauses: Boolean, prover: Prover ): Option[FOLFormula] = {
    val num = Utils.numeral( n )
    debug( "Calling findConseq …" )
    val M = findConseq( S, n, CSn, Set[Set[FOLClause]](), forgetClauses, prover ).toList.sortBy( l => ( l map ( _.length ) ).sum )
    debug( s"FindConseq found ${M.size} consequences." )

    val proofs = M.view.flatMap { F =>
      val C = And( F map { _.toFormula } )
      val pos = C.find( num ).toSet // If I understand the paper correctly, an improvement can be made here
      val posSets = pos.subsets().toList.sortBy( _.size ).reverse

      posSets.view.flatMap { P =>
        val Ctilde = ( C /: P )( ( acc, p ) => acc.replace( p, nu ).asInstanceOf[FOLFormula] )
        if ( S.solve( Ctilde ).isSolved( prover ) )
          Some( Ctilde )
        else
          None
      }
    }

    proofs.headOption
  }
}

class HeuristicSolutionFinder( n: Int, forgetClauses: Boolean = false, prover: Prover = VeriT ) extends SolutionFinder {
  override def findSolution( schematicSIP: SimpleInductionProof ): Option[FOLFormula] =
    FindFormulaH( schematicSIP, n, forgetClauses, prover )
}