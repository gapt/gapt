package at.logic.gapt.proofs.lkskNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import LKskProof._
import at.logic.gapt.proofs.lk.LKRuleCreationException

import scala.collection.mutable

object LKskProof {
  type Label = Seq[LambdaExpression]
  type LabelledFormula = ( Label, HOLFormula )
  type LabelledSequent = Sequent[LabelledFormula]
}

trait LKskProof extends SequentProof[LabelledFormula, LKskProof] with ContextRule[LabelledFormula, LKskProof] {
  def labels = conclusion map { _._1 }
  def formulas = conclusion map { _._2 }

  protected def requireEq[T]( a: T, b: T ) =
    require( a == b, s"$a == $b" )

  /**
   * Checks whether indices are in the right place and premise is defined at all of them.
   *
   * @param premise The sequent to be checked.
   * @param antecedentIndices Indices that should be in the antecedent.
   * @param succedentIndices Indices that should be in the succedent.
   */
  protected def validateIndices( premise: LabelledSequent, antecedentIndices: Seq[SequentIndex], succedentIndices: Seq[SequentIndex] ): Unit = {
    val antSet = mutable.HashSet[SequentIndex]()
    val sucSet = mutable.HashSet[SequentIndex]()

    for ( i <- antecedentIndices ) i match {
      case Ant( _ ) =>

        if ( !premise.isDefinedAt( i ) )
          throw LKRuleCreationException( s"Sequent $premise is not defined at index $i." )

        if ( antSet contains i )
          throw LKRuleCreationException( s"Duplicate index $i for sequent $premise." )

        antSet += i

      case Suc( _ ) => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
    }

    for ( i <- succedentIndices ) i match {
      case Suc( _ ) =>

        if ( !premise.isDefinedAt( i ) )
          throw LKRuleCreationException( s"Sequent $premise is not defined at index $i." )

        if ( sucSet contains i )
          throw LKRuleCreationException( s"Duplicate index $i for sequent $premise." )

        sucSet += i

      case Ant( _ ) => throw LKRuleCreationException( s"Index $i should be in the succedent." )
    }
  }

  private def LKRuleCreationException( message: String ): LKRuleCreationException = new LKRuleCreationException( longName, message )

}

trait InitialSequent extends LKskProof {
  def immediateSubProofs = Seq()
  def auxIndices = Seq()
}

case class Axiom( antLabel: Label, sucLabel: Label, atom: HOLFormula ) extends InitialSequent {
  def mainFormulaSequent = ( antLabel -> atom ) +: Sequent() :+ ( sucLabel -> atom )
}

case class EquationalAxiom( label: Label, atom: HOLAtom ) extends InitialSequent {
  require(
    atom match { case Eq( _, _ ) => true; case _ => false },
    "An equational axiom needs to be constructed from an equation!"
  )

  def mainFormulaSequent = Sequent() :+ ( label -> atom )
}

case class Reflexivity( label: Label, term: LambdaExpression ) extends InitialSequent {
  def mainFormulaSequent = Sequent() :+ ( label -> Eq( term, term ) )
}

case class BottomLeft( label: Label ) extends InitialSequent {
  def mainFormulaSequent = ( label -> Bottom() ) +: Sequent()
}

case class TopRight( label: Label ) extends InitialSequent {
  def mainFormulaSequent = Sequent() :+ ( label -> Top() )
}

case class TheoryAxiom( sequent: Sequent[LabelledFormula] ) extends InitialSequent {
  def mainFormulaSequent = sequent
}

trait UnaryRule extends LKskProof {
  def subProof: LKskProof
  def immediateSubProofs = Seq( subProof )
  def premise = subProof.conclusion
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
  requireEq( subProof.conclusion( aux1 ), subProof.conclusion( aux2 ) )
  val mainFormulaSequent = subProof.conclusion( aux1 ) +: Sequent()
  def auxIndices = Seq( Seq( aux1, aux2 ) )
}

case class ContractionRight( subProof: LKskProof, aux1: Suc, aux2: Suc ) extends UnaryRule {
  require( aux1 != aux2 )
  requireEq( subProof.conclusion( aux1 ), subProof.conclusion( aux2 ) )
  val mainFormulaSequent = Sequent() :+ subProof.conclusion( aux1 )
  def auxIndices = Seq( Seq( aux1, aux2 ) )
}

trait SameLabel extends LKskProof {
  def newFormulas: Sequent[HOLFormula]

  val label: Label = ( immediateSubProofs zip auxIndices ) flatMap {
    case ( p, auxs ) => auxs map { p.labels( _ ) }
  } head

  ( immediateSubProofs zip auxIndices ) foreach {
    case ( p, auxs ) => auxs foreach { aux => requireEq( p.labels( aux ), label ) }
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

case class Equality( subProof: LKskProof, eq: Ant, aux: SequentIndex, leftToRight: Boolean, pos: Seq[LambdaPosition] ) extends UnaryRule with SameLabel {
  require( eq != aux )

  lazy val ( s, t ) = subProof.formulas( eq ) match {
    case Eq( s_, t_ ) => if ( leftToRight ) s_ -> t_ else t_ -> s_
  }
  require( subProof.formulas( aux )( pos ) == s )
  lazy val mainFormula = subProof.formulas( aux ).replace( pos, t ).asInstanceOf[HOLFormula]

  lazy val newFormulas = if ( aux isAnt ) mainFormula +: Sequent() else Sequent() :+ mainFormula

  def auxIndices = Seq( Seq( aux ) )
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
  requireEq( subProof1.formulas( aux1 ), subProof2.formulas( aux2 ) ) // labels are not required to be equal
  def cutFormula = subProof1.formulas( aux1 )
  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )
  def mainFormulaSequent = Sequent()
}

//quantifier rules working on end-sequent ancestors.
case class AllSkLeft( subProof: LKskProof, aux: Ant, mainFormula: HOLFormula, substitutionTerm: LambdaExpression ) extends UnaryRule {
  val All( quantVar, formula ) = mainFormula
  val ( otherLabels :+ `substitutionTerm` ) = subProof.labels( aux )
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> substitutionTerm )( formula ) ) )

  val mainFormulaSequent = ( otherLabels -> mainFormula ) +: Sequent()

  def auxIndices = Seq( Seq( aux ) )
}

case class ExSkRight( subProof: LKskProof, aux: Suc, mainFormula: HOLFormula, substitutionTerm: LambdaExpression ) extends UnaryRule {
  val Ex( quantVar, formula ) = mainFormula
  val ( otherLabels :+ `substitutionTerm` ) = subProof.labels( aux )
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> substitutionTerm )( formula ) ) )

  val mainFormulaSequent = Sequent() :+ ( otherLabels -> mainFormula )
  def auxIndices = Seq( Seq( aux ) )
}

/* TODO: how to verify skolem symbols?
   They are quite flexible - the main restriction is that quantifiers cannot be contracted,
   when they were introduced from different skolem symbols */
case class AllSkRight( subProof: LKskProof, aux: Suc, mainFormula: HOLFormula, skolemSymbol: Const ) extends UnaryRule with SameLabel {
  val All( quantVar, formula ) = mainFormula
  val skolemTerm = skolemSymbol( subProof.labels( aux ): _* )
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> skolemTerm )( formula ) ) )

  lazy val newFormulas = Sequent() :+ mainFormula
  def auxIndices = Seq( Seq( aux ) )
}

case class ExSkLeft( subProof: LKskProof, aux: Ant, mainFormula: HOLFormula, skolemSymbol: Const ) extends UnaryRule with SameLabel {
  val Ex( quantVar, formula ) = mainFormula
  val skolemTerm = skolemSymbol( subProof.labels( aux ): _* )
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> skolemTerm )( formula ) ) )

  lazy val newFormulas = mainFormula +: Sequent()
  def auxIndices = Seq( Seq( aux ) )
}

//quantifier rules working on cut-ancestors.
case class AllRight( subProof: LKskProof, aux: Suc, mainFormula: HOLFormula, eigenVar: Var ) extends UnaryRule with SameLabel {
  val All( quantVar, formula ) = mainFormula
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> eigenVar )( formula ) ) )
  require( !( freeVariables( contexts.flatMap( _.elements ).map( _._2 ) ) contains eigenVar ) )

  lazy val newFormulas = Sequent() :+ mainFormula
  def auxIndices = Seq( Seq( aux ) )
}

case class ExLeft( subProof: LKskProof, aux: Ant, mainFormula: HOLFormula, eigenVar: Var ) extends UnaryRule with SameLabel {
  val Ex( quantVar, formula ) = mainFormula
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> eigenVar )( formula ) ) )
  require( !( freeVariables( contexts.flatMap( _.elements ).map( _._2 ) ) contains eigenVar ) )

  lazy val newFormulas = mainFormula +: Sequent()
  def auxIndices = Seq( Seq( aux ) )
}

case class AllLeft( subProof: LKskProof, aux: Ant, mainFormula: HOLFormula, substitutionTerm: LambdaExpression ) extends UnaryRule {
  val All( quantVar, formula ) = mainFormula
  val ( otherLabels :+ `substitutionTerm` ) = subProof.labels( aux )
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> substitutionTerm )( formula ) ) )

  val mainFormulaSequent = ( otherLabels -> mainFormula ) +: Sequent()

  def auxIndices = Seq( Seq( aux ) )
}

case class ExRight( subProof: LKskProof, aux: Suc, mainFormula: HOLFormula, substitutionTerm: LambdaExpression ) extends UnaryRule {
  val Ex( quantVar, formula ) = mainFormula
  val ( otherLabels :+ `substitutionTerm` ) = subProof.labels( aux )
  requireEq( subProof.formulas( aux ), BetaReduction.betaNormalize( Substitution( quantVar -> substitutionTerm )( formula ) ) )

  val mainFormulaSequent = Sequent() :+ ( otherLabels -> mainFormula )
  def auxIndices = Seq( Seq( aux ) )
}
