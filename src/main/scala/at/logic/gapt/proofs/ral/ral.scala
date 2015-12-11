package at.logic.gapt.proofs.ral

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.TypeSynonyms.SkolemSymbol
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.proofs._
import RalProof._

object RalProof {
  type Label = Seq[LambdaExpression]

  def Label( instances: LambdaExpression* ) = Seq( instances: _* )
}

trait RalProof extends SequentProof[( Label, HOLFormula ), RalProof] {
  def labels: Sequent[Label] = conclusion map { _._1 }
  def formulas: Sequent[HOLFormula] = conclusion map { _._2 }
}

case class RalInitial( conclusion: Sequent[( Label, HOLFormula )] ) extends RalProof {
  override def occConnectors = Seq()

  override def mainIndices = conclusion.indices
  override def auxIndices = Seq()

  override def immediateSubProofs = Seq()
}

case class RalCut( subProof1: RalProof, indices1: Seq[SequentIndex],
                   subProof2: RalProof, indices2: Seq[SequentIndex] ) extends RalProof {
  val cutFormula = subProof1.formulas( indices1 head )

  indices1 foreach { i1 =>
    require( i1 isSuc )
    require( subProof1.formulas( i1 ) == cutFormula )
  }
  indices2 foreach { i2 =>
    require( i2 isAnt )
    require( subProof2.formulas( i2 ) == cutFormula )
  }

  override val conclusion = ( subProof1.conclusion delete indices1 ) ++ ( subProof2.conclusion delete indices2 )

  override def occConnectors = Seq(
    OccConnector( conclusion, subProof1.conclusion,
      ( subProof1.conclusion.indicesSequent delete indices1 map { Seq( _ ) } ) ++ ( subProof2.conclusion.indicesSequent delete indices2 map { _ => Seq() } ) ),
    OccConnector( conclusion, subProof2.conclusion,
      ( subProof1.conclusion.indicesSequent delete indices1 map { _ => Seq() } ) ++ ( subProof2.conclusion.indicesSequent delete indices2 map { Seq( _ ) } ) )
  )

  override def mainIndices = Seq()
  override def auxIndices = Seq( indices1, indices2 )

  override def immediateSubProofs = Seq( subProof1, subProof2 )
}

case class RalSub( subProof: RalProof, substitution: Substitution ) extends RalProof {
  override val conclusion = subProof.conclusion map {
    case ( label, formula ) =>
      ( label map { sk => BetaReduction.betaNormalize( substitution( sk ) ) } ) ->
        BetaReduction.betaNormalize( substitution( formula ) )
  }

  override def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion,
    subProof.conclusion.indicesSequent.map { Seq( _ ) } ) )

  override def mainIndices = conclusion.indices
  override def auxIndices = Seq( subProof.conclusion.indices )

  override def immediateSubProofs = Seq( subProof )
}

case class RalFactor( subProof: RalProof, idx1: SequentIndex, idx2: SequentIndex ) extends RalProof {
  require( idx1 sameSideAs idx2 )
  require( subProof.conclusion( idx1 ) == subProof.conclusion( idx2 ) ) // TODO: do the labels have to be the same as well?
  require( isAtom( subProof.formulas( idx1 ) ) )
  require( isAtom( subProof.formulas( idx2 ) ) )

  override val conclusion = subProof.conclusion delete idx2

  override def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion,
    subProof.conclusion.indicesSequent.
      map { Seq( _ ) }.
      updated( idx1, Seq( idx1, idx2 ) ).
      delete( idx2 ) ) )

  override def mainIndices = occConnectors.head.children( idx1 )
  override def auxIndices = Seq( Seq( idx1, idx2 ) )

  override def immediateSubProofs = Seq( subProof )
}

case class RalPara( subProof1: RalProof, equation: Suc,
                    subProof2: RalProof, modulant: SequentIndex,
                    positions: Seq[LambdaPosition], leftToRight: Boolean ) extends RalProof {
  require( equation isSuc )
  val ( t, s ) = ( subProof1.formulas( equation ), leftToRight ) match {
    case ( Eq( a, b ), true )  => ( a, b )
    case ( Eq( a, b ), false ) => ( b, a )
  }

  positions foreach { position =>
    require( subProof2.formulas( modulant )( position ) == t )
  }

  require( subProof1.labels( equation ) == subProof2.labels( modulant ) )

  override val conclusion = subProof1.conclusion.delete( equation ) ++
    subProof2.conclusion.updated(
      modulant,
      subProof2.labels( modulant ) ->
        positions.foldLeft( subProof2.formulas( modulant ) ) { _.replace( _, s ).asInstanceOf[HOLFormula] }
    )

  override def occConnectors = Seq(
    OccConnector( conclusion, subProof1.conclusion,
      subProof1.conclusion.indicesSequent.delete( equation ).map { Seq( _ ) } ++ subProof2.conclusion.indicesSequent.map { _ => Seq() } ),
    OccConnector( conclusion, subProof2.conclusion,
      subProof1.conclusion.indicesSequent.delete( equation ).map { _ => Seq() } ++ subProof2.conclusion.indicesSequent.map { Seq( _ ) } )
  )

  override def mainIndices = occConnectors( 1 ).children( modulant )
  override def auxIndices = Seq( Seq( equation ), Seq( modulant ) )

  override def immediateSubProofs = Seq( subProof1, subProof2 )
}

private[ral] trait OneFormulaRule extends RalProof with ContextRule[( Label, HOLFormula ), RalProof] {
  def subProof: RalProof
  def idx: SequentIndex

  def newLabelledFormulas: Sequent[( Label, HOLFormula )]

  override def mainFormulaSequent = newLabelledFormulas

  override def auxIndices = Seq( Seq( idx ) )

  override def immediateSubProofs = Seq( subProof )
}

private[ral] trait SimpleOneFormulaRule extends OneFormulaRule {
  def newFormulas: Sequent[HOLFormula]
  override def newLabelledFormulas = newFormulas map { subProof.labels( idx ) -> _ }
}

private[ral] object computeSkolemTerm {
  def apply( sk: SkolemSymbol, t: Ty, label: Label ) = {
    val labelList = label.toList
    val tp = FunctionType( t, labelList map { _.exptype } )
    HOLFunction( Const( sk, tp ), labelList )
  }
}

case class RalAllT( subProof: RalProof, idx: SequentIndex, eigenVariable: Var ) extends OneFormulaRule {
  require( idx isSuc )
  lazy val App( ForallC( _ ), sub ) = subProof.formulas( idx )

  override val newLabelledFormulas = Sequent() :+
    ( eigenVariable +: subProof.labels( idx ) ) ->
    BetaReduction.betaNormalize( App( sub, eigenVariable ).asInstanceOf[HOLFormula] )
}

case class RalAllF( subProof: RalProof, idx: SequentIndex, skolemSymbol: SkolemSymbol ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  lazy val App( ForallC( quantifiedType ), sub ) = subProof.formulas( idx )

  lazy val skolemTerm = computeSkolemTerm( skolemSymbol, quantifiedType, subProof.labels( idx ) )
  override val newFormulas = BetaReduction.betaNormalize( App( sub, skolemTerm ).asInstanceOf[HOLFormula] ) +: Sequent()
}

case class RalExF( subProof: RalProof, idx: SequentIndex, eigenVariable: Var ) extends OneFormulaRule {
  require( idx isAnt )
  lazy val App( ExistsC( _ ), sub ) = subProof.formulas( idx )

  override val newLabelledFormulas =
    ( ( eigenVariable +: subProof.labels( idx ) ) ->
      BetaReduction.betaNormalize( App( sub, eigenVariable ).asInstanceOf[HOLFormula] ) ) +: Sequent()
}

case class RalExT( subProof: RalProof, idx: SequentIndex, skolemSymbol: SkolemSymbol ) extends SimpleOneFormulaRule {
  require( idx isSuc )
  lazy val App( ExistsC( quantifiedType ), sub ) = subProof.formulas( idx )

  lazy val skolemTerm = computeSkolemTerm( skolemSymbol, quantifiedType, subProof.labels( idx ) )
  override val newFormulas = Sequent() :+ BetaReduction.betaNormalize( App( sub, skolemTerm ).asInstanceOf[HOLFormula] )
}

case class RalTopF( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  require( subProof.formulas( idx ) == Top() )

  override val newFormulas = Sequent()
}

case class RalBottomT( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isSuc )
  require( subProof.formulas( idx ) == Bottom() )

  override val newFormulas = Sequent()
}

case class RalNegF( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  lazy val Neg( sub ) = subProof.formulas( idx )

  override val newFormulas = Sequent() :+ sub
}

case class RalNegT( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isSuc )
  lazy val Neg( sub ) = subProof.formulas( idx )

  override val newFormulas = sub +: Sequent()
}

case class RalAndT1( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isSuc )
  lazy val And( sub1, _ ) = subProof.formulas( idx )

  override val newFormulas = Sequent() :+ sub1
}

case class RalAndT2( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isSuc )
  lazy val And( _, sub2 ) = subProof.formulas( idx )

  override val newFormulas = Sequent() :+ sub2
}

case class RalOrF1( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  lazy val Or( sub1, _ ) = subProof.formulas( idx )

  override val newFormulas = sub1 +: Sequent()
}

case class RalOrF2( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  lazy val Or( _, sub2 ) = subProof.formulas( idx )

  override val newFormulas = sub2 +: Sequent()
}

case class RalImpF1( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  lazy val Imp( l, _ ) = subProof.formulas( idx )

  override val newFormulas = Sequent() :+ l
}

case class RalImpF2( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  lazy val Imp( _, r ) = subProof.formulas( idx )

  override val newFormulas = r +: Sequent()
}

case class RalAndF( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isAnt )
  lazy val And( l, r ) = subProof.formulas( idx )

  override val newFormulas = l +: r +: Sequent()
}

case class RalOrT( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isSuc )
  lazy val Or( l, r ) = subProof.formulas( idx )

  override val newFormulas = Sequent() :+ l :+ r
}

case class RalImpT( subProof: RalProof, idx: SequentIndex ) extends SimpleOneFormulaRule {
  require( idx isSuc )
  lazy val Imp( l, r ) = subProof.formulas( idx )

  override val newFormulas = l +: Sequent() :+ r
}
