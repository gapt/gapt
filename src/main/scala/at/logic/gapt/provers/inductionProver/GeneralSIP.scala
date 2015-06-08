package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.expansionTrees.{ toDeep, ExpansionSequent }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.{ LKProof, FSequent }

class GeneralSIP( val ExpSeq0: ExpansionSequent, val ExpSeq1: ExpansionSequent, val ExpSeq2: ExpansionSequent, val B: FOLFormula, val t: List[FOLTerm], val u: List[FOLTerm] ) {
  import GeneralSIP._

  require( ExpSeq0.succedent.isEmpty, "Right-hand side of ExpSeq0 is nonempty" )
  require( ExpSeq1.succedent.isEmpty, "Right-hand side of ExpSeq1 is nonempty" )
  require( ExpSeq2.succedent.isEmpty, "Right-hand side of ExpSeq2 is nonempty" )

  val Gamma0 = toDeep( ExpSeq0 ).antecedent.toList.asInstanceOf[List[FOLFormula]]
  val Gamma1 = toDeep( ExpSeq1 ).antecedent.toList.asInstanceOf[List[FOLFormula]]
  val Gamma2 = toDeep( ExpSeq2 ).antecedent.toList.asInstanceOf[List[FOLFormula]]

  require( List( alpha, beta ) contains freeVariables( Gamma0 ), "Gamma0 contains free variables other than α, β" )
  require( List( alpha, nu, gamma ) contains freeVariables( Gamma1 ), "Gamma1 contains free variables other than α, ν, γ" )
  require( List( alpha ) contains freeVariables( Gamma2 ), "Gamma2 contains free variables other than α" )
  require( List( alpha ) contains freeVariables( B ), "B contains free variables other than α" )

  require( List( alpha ) contains freeVariables( u ), "A term in u contains free variables other than α" )
  require( List( alpha, nu, gamma ) contains freeVariables( t ), "A term in t contains free variables other than α, ν, γ" )
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

  require( List( alpha, nu, gamma ) contains freeVariables( inductionFormula ), "inductionFormula contains free variables other than α, ν, γ" )

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
    val inductionBaseAxiom = Axiom( Sequent0 )
    val inductionBase1 = ForallRightRule( inductionBaseAxiom, F( alpha, zero, beta ), All( y, F( alpha, zero, y ) ), gamma )

    val inductionStepAxiom = Axiom( Sequent1 )
    val inductionStep1 = ForallRightRule( inductionStepAxiom, F( alpha, snu, gamma ), All( y, F( alpha, snu, y ) ), gamma )
    val inductionStep2 = t.foldLeft( inductionStep1 ) {
      ( acc, ti ) => ForallLeftRule( acc, F( alpha, nu, ti ), All( y, F( alpha, nu, y ) ), ti )
    }
    val inductionStep3 = ContractionLeftMacroRule( inductionStep2, All( y, F( alpha, nu, y ) ) )

    val conclusionAxiom = Axiom( Sequent2 )
    val conclusion1 = u.foldLeft( conclusionAxiom.asInstanceOf[LKProof] ) {
      ( acc: LKProof, ui ) => ForallLeftRule( acc, F( alpha, alpha, ui ), All( y, F( alpha, alpha, y ) ), ui )
    }
    val conclusion2 = ContractionLeftMacroRule( conclusion1, All( y, F( alpha, alpha, y ) ) )

    val inductionProof = InductionRule( inductionBase1, inductionStep3, All( y, F( alpha, zero, y ) ), All( y, F( alpha, nu, y ) ), All( y, F( alpha, snu, y ) ), alpha )

    CutRule( inductionProof, conclusion2, All( y, F( alpha, alpha, y ) ) )
  }
}

object SimpleInductionProof {
  val y = FOLVar( "y" )

}