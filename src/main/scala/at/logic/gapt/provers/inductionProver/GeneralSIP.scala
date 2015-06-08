package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.expansionTrees.{ toDeep, ExpansionSequent }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.{ LKProof, FSequent }
import at.logic.gapt.provers.prover9.Prover9Prover

class GeneralSIP( val ExpSeq0: ExpansionSequent, val ExpSeq1: ExpansionSequent, val ExpSeq2: ExpansionSequent, val B: FOLFormula, val t: List[FOLTerm], val u: List[FOLTerm] ) {
  import GeneralSIP._

  require( ExpSeq0.succedent.isEmpty, "Right-hand side of ExpSeq0 is nonempty" )
  require( ExpSeq1.succedent.isEmpty, "Right-hand side of ExpSeq1 is nonempty" )
  require( ExpSeq2.succedent.isEmpty, "Right-hand side of ExpSeq2 is nonempty" )

  val Gamma0 = toDeep( ExpSeq0 ).antecedent.toList.asInstanceOf[List[FOLFormula]]
  val Gamma1 = toDeep( ExpSeq1 ).antecedent.toList.asInstanceOf[List[FOLFormula]]
  val Gamma2 = toDeep( ExpSeq2 ).antecedent.toList.asInstanceOf[List[FOLFormula]]

  require( freeVariables( Gamma0 ) subsetOf Set( alpha, beta ), freeVariables( Gamma0 ).toString )
  require( freeVariables( Gamma1 ) subsetOf Set( alpha, nu, gamma ), freeVariables( Gamma1 ).toString )
  require( freeVariables( Gamma2 ) subsetOf Set( alpha ), freeVariables( Gamma2 ).toString )
  require( freeVariables( B ) subsetOf Set( alpha ), "B contains free variables other than α" )

  require( freeVariables( u ) subsetOf Set( alpha ), "A term in u contains free variables other than α" )
  require( freeVariables( t ) subsetOf Set( alpha, nu, gamma ), "A term in t contains free variables other than α, ν, γ" )
}

object GeneralSIP {
  val zero = FOLConst( "0" )
  val alpha = FOLVar( "α" )
  val beta = FOLVar( "β" )
  val gamma = FOLVar( "γ" )
  val nu = FOLVar( "ν" )
  val snu = FOLFunction( "s", List( nu ) )

  def X( x1: FOLTerm, x2: FOLTerm, x3: FOLTerm ): HOLFormula = HOLAtom( Var( "X", Ti -> Ti -> Ti -> To ), x1, x2, x3 )
}

class SchematicSIP( ExpSeq0: ExpansionSequent, ExpSeq1: ExpansionSequent, ExpSeq2: ExpansionSequent, B: FOLFormula, t: List[FOLTerm], u: List[FOLTerm] ) extends GeneralSIP( ExpSeq0, ExpSeq1, ExpSeq2, B, t, u ) {

  import GeneralSIP._

  val Sequent0 = FSequent( Gamma0, List( X( alpha, zero, beta ) ) )

  private val Xt = t map { X( alpha, nu, _ ) }
  val Sequent1 = FSequent( Gamma1 ++ Xt, List( X( alpha, snu, gamma ) ) )

  private val Xu = u map { X( alpha, alpha, _ ) }

  val Sequent2 = FSequent( Gamma2 ++ Xu, List( B ) )
}

class SimpleInductionProof( ExpSeq0: ExpansionSequent, ExpSeq1: ExpansionSequent, ExpSeq2: ExpansionSequent, B: FOLFormula, t: List[FOLTerm], u: List[FOLTerm], val inductionFormula: FOLFormula ) extends GeneralSIP( ExpSeq0, ExpSeq1, ExpSeq2, B, t, u ) {
  import GeneralSIP._
  import SimpleInductionProof._

  require( freeVariables( inductionFormula ) subsetOf Set( alpha, nu, gamma ), "inductionFormula contains free variables other than α, ν, γ" )

  private def F( x1: FOLTerm, x2: FOLTerm, x3: FOLTerm ): FOLFormula = {
    val sub = FOLSubstitution( List( alpha -> x1, nu -> x2, gamma -> x3 ) )
    sub( inductionFormula )
  }

  val Sequent0 = FSequent( Gamma0, List( F( alpha, zero, beta ) ) )

  val Ft = t map { F( alpha, nu, _ ) }
  val Sequent1 = FSequent( Gamma1 ++ Ft, List( F( alpha, snu, gamma ) ) )

  val Fu = u map { F( alpha, alpha, _ ) }
  val Sequent2 = FSequent( Gamma2 ++ Fu, List( B ) )

  def toLKProof: LKProof = {
    val p9prover = new Prover9Prover

    val pi0 = p9prover.getLKProof( Sequent0 ).get
    val inductionBase1 = proofFromInstances( pi0, ExpSeq0 )
    val inductionBase2 = ForallRightRule( inductionBase1, F( alpha, zero, beta ), All( y, F( alpha, zero, y ) ), beta )

    val pi1 = p9prover.getLKProof( Sequent1 ).get
    val inductionStep1 = proofFromInstances( pi1, ExpSeq1 )
    val inductionStep2 = t.foldLeft( inductionStep1 ) {
      ( acc, ti ) => ForallLeftRule( acc, F( alpha, nu, ti ), All( y, F( alpha, nu, y ) ), ti )
    }
    val inductionStep3 = ForallRightRule( inductionStep2, F( alpha, snu, gamma ), All( y, F( alpha, snu, y ) ), gamma )

    val inductionStep4 = ContractionLeftMacroRule( inductionStep3, All( y, F( alpha, nu, y ) ) )

    val pi2 = p9prover.getLKProof( Sequent2 ).get
    val conclusion1 = proofFromInstances( pi2, ExpSeq2 )
    val conclusion2 = u.foldLeft( conclusion1.asInstanceOf[LKProof] ) {
      ( acc: LKProof, ui ) => ForallLeftRule( acc, F( alpha, alpha, ui ), All( y, F( alpha, alpha, y ) ), ui )
    }
    val conclusion3 = ContractionLeftMacroRule( conclusion2, All( y, F( alpha, alpha, y ) ) )

    val inductionProof = InductionRule( inductionBase2, inductionStep4, All( y, F( alpha, zero, y ) ), All( y, F( alpha, nu, y ) ), All( y, F( alpha, snu, y ) ), alpha )

    CutRule( inductionProof, conclusion3, All( y, F( alpha, alpha, y ) ) )
  }
}

object SimpleInductionProof {
  val y = FOLVar( "y" )

}