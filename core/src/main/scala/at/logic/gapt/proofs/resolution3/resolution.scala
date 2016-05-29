package at.logic.gapt.proofs.resolution3

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ ContextRule, HOLSequent, OccConnector, Sequent, SequentIndex, SequentProof }

trait ResolutionProof extends SequentProof[HOLFormula, ResolutionProof]

abstract class LocalResolutionRule extends ResolutionProof with ContextRule[HOLFormula, ResolutionProof]

abstract class InitialClause extends LocalResolutionRule {
  override def auxIndices = Seq()
  override def immediateSubProofs = Seq()
}
case class Input( sequent: HOLSequent ) extends InitialClause {
  override def mainFormulaSequent = sequent
}
case class Taut( formula: HOLFormula ) extends InitialClause {
  override def mainFormulaSequent = formula +: Sequent() :+ formula
}
case class Refl( term: LambdaExpression ) extends InitialClause {
  override def mainFormulaSequent = Sequent() :+ ( term === term )
}
case class Definition( definedConstant: Const, definition: LambdaExpression ) extends InitialClause {
  val FunctionType( To, argTypes ) = definedConstant.exptype
  val boundVars = for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( s"x$i", t )

  override def mainFormulaSequent = Sequent() :+ All.Block(
    boundVars,
    definedConstant( boundVars: _* ) <-> BetaReduction.betaNormalize( definition( boundVars: _* ) )
  )
}

case class Factor( subProof: ResolutionProof, idx1: SequentIndex, idx2: SequentIndex ) extends LocalResolutionRule {
  require( idx1 sameSideAs idx2 )
  require( idx1 < idx2 )
  require( subProof.conclusion( idx1 ) == subProof.conclusion( idx2 ) )
  override def mainFormulaSequent =
    if ( idx1 isAnt ) subProof.conclusion( idx1 ) +: Sequent()
    else Sequent() :+ subProof.conclusion( idx1 )
  override def immediateSubProofs = Seq( subProof )
  override def auxIndices = Seq( Seq( idx1, idx2 ) )
}
object Factor {
  def apply( p: ResolutionProof ): ResolutionProof = {
    var p_ = p
    for ( ( a, i ) <- p.conclusion.diff( p.conclusion.distinct ).zipWithIndex ) {
      val Seq( j1, j2, _* ) = p_.conclusion.zipWithIndex.elements.filter( _._2 sameSideAs i ).filter( _._1 == a ).map( _._2 )
      p_ = Factor( p_, j1, j2 )
    }
    p_
  }
  def withOccConn( p: ResolutionProof ): ( ResolutionProof, OccConnector[HOLFormula] ) = {
    var p_ = p
    var conn = OccConnector( p_.conclusion )
    for ( ( a, i ) <- p.conclusion.diff( p.conclusion.distinct ).zipWithIndex ) {
      val Seq( j1, j2, _* ) = p_.conclusion.zipWithIndex.elements.filter( _._2 sameSideAs i ).filter( _._1 == a ).map( _._2 )
      p_ = Factor( p_, j1, j2 )
      conn = p_.occConnectors.head * conn
    }
    p_ -> conn
  }
}

case class Subst( subProof: ResolutionProof, substitution: Substitution ) extends ResolutionProof {
  override def conclusion: Sequent[HOLFormula] = subProof.conclusion.map( substitution( _ ) ).map( BetaReduction.betaNormalize )
  override def mainIndices: Seq[SequentIndex] = subProof.conclusion.indices
  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( subProof.conclusion.indices )
  override def occConnectors: Seq[OccConnector[HOLFormula]] =
    Seq( OccConnector( conclusion, subProof.conclusion, subProof.conclusion.indicesSequent.map( Seq( _ ) ) ) )
  override def immediateSubProofs: Seq[ResolutionProof] = Seq( subProof )
}

case class Resolution( subProof1: ResolutionProof, idx1: SequentIndex,
                       subProof2: ResolutionProof, idx2: SequentIndex ) extends LocalResolutionRule {
  require( idx1 isSuc )
  require( idx2 isAnt )
  require( subProof1.conclusion( idx1 ) == subProof2.conclusion( idx2 ) )

  def mainFormulaSequent = Sequent()
  def immediateSubProofs = Seq( subProof1, subProof2 )
  def auxIndices = Seq( Seq( idx1 ), Seq( idx2 ) )
}

case class Paramod( subProof1: ResolutionProof, eqIdx: SequentIndex, leftToRight: Boolean,
                    subProof2: ResolutionProof, auxIdx: SequentIndex,
                    context: LambdaExpression ) extends LocalResolutionRule {
  require( eqIdx isSuc )
  val ( t, s ) = subProof1.conclusion( eqIdx ) match { case Eq( t_, s_ ) => if ( leftToRight ) ( t_, s_ ) else ( s_, t_ ) }

  def auxFormula = subProof2.conclusion( auxIdx )
  require( auxFormula == BetaReduction.betaNormalize( context( t ) ) )
  val rewrittenAuxFormula = BetaReduction.betaNormalize( context( s ) ).asInstanceOf[HOLFormula]
  def mainFormulaSequent =
    if ( auxIdx isAnt ) rewrittenAuxFormula +: Sequent()
    else Sequent() :+ rewrittenAuxFormula

  def immediateSubProofs = Seq( subProof1, subProof2 )
  def auxIndices = Seq( Seq( eqIdx ), Seq( auxIdx ) )
}

abstract class PropositionalResolutionRule extends LocalResolutionRule {
  def subProof: ResolutionProof
  def idx: SequentIndex

  override def immediateSubProofs = Seq( subProof )
  override def auxIndices = Seq( Seq( idx ) )
}

case class DefIntro( subProof: ResolutionProof, idx: SequentIndex,
                     defAtom: HOLAtom, definition: LambdaExpression ) extends PropositionalResolutionRule {
  val Apps( defConst: HOLAtomConst, defArgs ) = defAtom
  require( subProof.conclusion( idx ) == BetaReduction.betaNormalize( definition( defArgs: _* ) ) )
  override def mainFormulaSequent =
    if ( idx isAnt ) defAtom +: Sequent()
    else Sequent() :+ defAtom
}

case class TopL( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Top() = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent()
}
case class BottomR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Bottom() = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent()
}
case class NegL( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Neg( sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub
}
case class NegR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Neg( sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub +: Sequent()
}
case class AndL( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val And( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub1 +: sub2 +: Sequent()
}
case class OrR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Or( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub1 :+ sub2
}
case class ImpR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Imp( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub1 +: Sequent() :+ sub2
}
case class AndR1( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val And( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub1
}
case class OrL1( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Or( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub1 +: Sequent()
}
case class ImpL1( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Imp( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub1
}
case class AndR2( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val And( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub2
}
case class OrL2( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Or( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub2 +: Sequent()
}
case class ImpL2( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Imp( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub2 +: Sequent()
}

abstract class WeakQuantResolutionRule extends PropositionalResolutionRule {
  def variable: Var
  def bound: Var
  def sub: HOLFormula
  def instFormula = Substitution( bound -> variable )( sub )

  // FIXME: is eigenvariable condition a good idea?
  require( !freeVariables( subProof.conclusion ).contains( variable ) )
}
case class AllR( subProof: ResolutionProof, idx: SequentIndex, variable: Var ) extends WeakQuantResolutionRule {
  require( idx isSuc )
  val All( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ instFormula
}
object AllR {
  object Block {
    def apply( subProof: ResolutionProof, idx: SequentIndex, vars: Seq[Var] ): ResolutionProof = vars match {
      case v +: vs =>
        apply( AllR( subProof, idx, v ), subProof.conclusion.indices.last, vs )
      case Seq() => subProof
    }
    def apply( subProof: ResolutionProof, idx: SequentIndex ): ResolutionProof = {
      val All.Block( vs, _ ) = subProof.conclusion( idx )
      apply( subProof, idx, vs )
    }
  }
}
case class ExL( subProof: ResolutionProof, idx: SequentIndex, variable: Var ) extends WeakQuantResolutionRule {
  require( idx isAnt )
  val Ex( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = instFormula +: Sequent()
}

abstract class SkolemQuantResolutionRule extends PropositionalResolutionRule {
  def skolemTerm: LambdaExpression
  def skolemDef: LambdaExpression
  def bound: Var
  def sub: HOLFormula

  val Apps( skolemConst: Const, skolemArgs ) = skolemTerm
  require( BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) ) == subProof.conclusion( idx ) )

  def instFormula = Substitution( bound -> skolemTerm )( sub )
}
case class AllL( subProof: ResolutionProof, idx: SequentIndex, skolemTerm: LambdaExpression, skolemDef: LambdaExpression ) extends SkolemQuantResolutionRule {
  require( idx isAnt )
  val All( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = instFormula +: Sequent()
}
case class ExR( subProof: ResolutionProof, idx: SequentIndex, skolemTerm: LambdaExpression, skolemDef: LambdaExpression ) extends SkolemQuantResolutionRule {
  require( idx isSuc )
  val Ex( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ instFormula
}
