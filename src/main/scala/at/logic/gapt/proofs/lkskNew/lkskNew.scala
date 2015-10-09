package at.logic.gapt.proofs.lkskNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import LKskProof._

object LKskProof {
  type Label = Seq[LambdaExpression]
  type LabelledFormula = ( Label, HOLFormula )
}

trait LKskProof extends SequentProof[LabelledFormula, LKskProof] with ContextRule[LabelledFormula, LKskProof] {
  def labels = conclusion map { _._1 }
  def formulas = conclusion map { _._2 }
}

trait InitialSequent extends LKskProof {
  def immediateSubProofs = Seq()
  def auxIndices = Seq()
}

case class LogicalAxiom( label: Label, atom: HOLAtom ) extends InitialSequent {
  val labelledAtom = label -> atom
  def mainFormulaSequent = labelledAtom +: Sequent() :+ labelledAtom
}

case class BottomLeft( label: Label ) extends InitialSequent {
  def mainFormulaSequent = ( label -> Bottom() ) +: Sequent()
}

case class TopRight( label: Label ) extends InitialSequent {
  def mainFormulaSequent = Sequent() :+ ( label -> Top() )
}

trait UnaryRule extends LKskProof {
  def subProof: LKskProof
  def immediateSubProofs = Seq( subProof )
}

case class WeakeningLeft( subProof: LKskProof, weakLabelledFormula: LabelledFormula ) extends UnaryRule {
  val mainFormulaSequent = weakLabelledFormula +: Sequent()
  def auxIndices = Seq( Seq() )
}

case class WeakeningRight( subProof: LKskProof, weakLabelledFormula: LabelledFormula ) extends UnaryRule {
  val mainFormulaSequent = Sequent() :+ weakLabelledFormula
  def auxIndices = Seq( Seq() )
}

case class ContractionLeft( subProof: LKskProof, aux1: Ant, aux2: Ant ) extends UnaryRule {
  require( aux1 != aux2 )
  require( subProof.conclusion( aux1 ) == subProof.conclusion( aux2 ) )
  val mainFormulaSequent = subProof.conclusion( aux1 ) +: Sequent()
  def auxIndices = Seq( Seq( aux1, aux2 ) )
}

case class ContractionRight( subProof: LKskProof, aux1: Suc, aux2: Suc ) extends UnaryRule {
  require( aux1 != aux2 )
  require( subProof.conclusion( aux1 ) == subProof.conclusion( aux2 ) )
  val mainFormulaSequent = Sequent() :+ subProof.conclusion( aux1 )
  def auxIndices = Seq( Seq( aux1, aux2 ) )
}

trait SameLabel extends LKskProof {
  def newFormulas: Sequent[HOLFormula]

  val label: Label = ( immediateSubProofs zip auxIndices ) flatMap {
    case ( p, auxs ) => auxs map { p.labels( _ ) }
  } head

  ( immediateSubProofs zip auxIndices ) foreach {
    case ( p, auxs ) => auxs foreach { aux => require( p.labels( aux ) == label ) }
  }

  val mainFormulaSequent = newFormulas map { label -> _ }
}

case class NegLeft( subProof: LKskProof, aux: Suc ) extends UnaryRule with SameLabel {
  lazy val newFormulas = -subProof.formulas( aux ) +: Sequent()
  def auxIndices = Seq( Seq( aux ) )
}

case class NegRight( subProof: LKskProof, aux: Ant ) extends UnaryRule with SameLabel {
  lazy val newFormulas = Sequent() :+ -subProof.formulas( aux )
  def auxIndices = Seq( Seq( aux ) )
}

case class AndLeft( subProof: LKskProof, aux1: Ant, aux2: Ant ) extends UnaryRule with SameLabel {
  require( aux1 != aux2 )
  lazy val newFormulas = ( subProof.formulas( aux1 ) & subProof.formulas( aux2 ) ) +: Sequent()
  def auxIndices = Seq( Seq( aux1, aux2 ) )
}

case class OrRight( subProof: LKskProof, aux1: Suc, aux2: Suc ) extends UnaryRule with SameLabel {
  require( aux1 != aux2 )
  lazy val newFormulas = Sequent() :+ ( subProof.formulas( aux1 ) | subProof.formulas( aux2 ) )
  def auxIndices = Seq( Seq( aux1, aux2 ) )
}

case class ImpRight( subProof: LKskProof, aux1: Ant, aux2: Suc ) extends UnaryRule with SameLabel {
  lazy val newFormulas = Sequent() :+ ( subProof.formulas( aux1 ) --> subProof.formulas( aux2 ) )
  def auxIndices = Seq( Seq( aux1, aux2 ) )
}

trait BinaryRule extends LKskProof {
  def subProof1: LKskProof
  def subProof2: LKskProof
  def immediateSubProofs = Seq( subProof1, subProof2 )
}

case class AndRight( subProof1: LKskProof, aux1: Suc, subProof2: LKskProof, aux2: Suc ) extends BinaryRule with SameLabel {
  lazy val newFormulas = Sequent() :+ ( subProof1.formulas( aux1 ) & subProof2.formulas( aux2 ) )
  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )
}

case class OrLeft( subProof1: LKskProof, aux1: Ant, subProof2: LKskProof, aux2: Ant ) extends BinaryRule with SameLabel {
  lazy val newFormulas = ( subProof1.formulas( aux1 ) | subProof2.formulas( aux2 ) ) +: Sequent()
  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )
}

case class ImpLeft( subProof1: LKskProof, aux1: Suc, subProof2: LKskProof, aux2: Ant ) extends BinaryRule with SameLabel {
  lazy val newFormulas = ( subProof1.formulas( aux1 ) --> subProof2.formulas( aux2 ) ) +: Sequent()
  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )
}

case class Cut( subProof1: LKskProof, aux1: Suc, subProof2: LKskProof, aux2: Ant ) extends BinaryRule {
  require( subProof1.formulas( aux1 ) == subProof2.formulas( aux2 ) ) // labels are not required to be equal
  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )
  def mainFormulaSequent = Sequent()
}

case class AllLeft( subProof: LKskProof, aux: Ant, mainFormula: HOLFormula, substitutionTerm: LambdaExpression ) extends UnaryRule {
  val All( quantVar, formula ) = mainFormula
  val ( otherLabels :+ `substitutionTerm` ) = subProof.labels( aux )
  require( subProof.formulas( aux ) == BetaReduction.betaNormalize( Substitution( quantVar -> substitutionTerm )( formula ) ) )

  val mainFormulaSequent = ( otherLabels -> mainFormula ) +: Sequent()

  def auxIndices = Seq( Seq( aux ) )
}

case class ExRight( subProof: LKskProof, aux: Suc, mainFormula: HOLFormula, substitutionTerm: LambdaExpression ) extends UnaryRule {
  val Ex( quantVar, formula ) = mainFormula
  val ( otherLabels :+ `substitutionTerm` ) = subProof.labels( aux )
  require( subProof.formulas( aux ) == BetaReduction.betaNormalize( Substitution( quantVar -> substitutionTerm )( formula ) ) )

  val mainFormulaSequent = Sequent() :+ ( otherLabels -> mainFormula )
  def auxIndices = Seq( Seq( aux ) )
}

// TODO: how to verify skolem symbols?

case class AllRight( subProof: LKskProof, aux: Suc, mainFormula: HOLFormula, skolemSymbol: Const ) extends UnaryRule with SameLabel {
  val All( quantVar, formula ) = mainFormula
  val skolemTerm = skolemSymbol( subProof.labels( aux ): _* )
  require( subProof.formulas( aux ) == BetaReduction.betaNormalize( Substitution( quantVar -> skolemTerm )( formula ) ) )

  lazy val newFormulas = Sequent() :+ mainFormula
  def auxIndices = Seq( Seq( aux ) )
}

case class ExLeft( subProof: LKskProof, aux: Ant, mainFormula: HOLFormula, skolemSymbol: Const ) extends UnaryRule with SameLabel {
  val Ex( quantVar, formula ) = mainFormula
  val skolemTerm = skolemSymbol( subProof.labels( aux ): _* )
  require( subProof.formulas( aux ) == BetaReduction.betaNormalize( Substitution( quantVar -> skolemTerm )( formula ) ) )

  lazy val newFormulas = mainFormula +: Sequent()
  def auxIndices = Seq( Seq( aux ) )
}
