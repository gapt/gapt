package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, SkolemSymbolFactory }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkskNew.LKskProof._
import at.logic.gapt.proofs.lkskNew
import at.logic.gapt.proofs.lk
import at.logic.gapt.proofs.lkskNew._

class LKToLKsk( skolemSymbolFactory: SkolemSymbolFactory ) {
  def apply( p: LKProof ): LKskProof = apply( p, p.conclusion map { _ => Seq() }, p.conclusion map { _ => false } )

  def apply( p: LKProof, labels: Sequent[Label], isCutAnc: Sequent[Boolean] ): LKskProof = {
    val res = p match {
      case LogicalAxiom( atom )     => lkskNew.Axiom( labels( Ant( 0 ) ), labels( Suc( 0 ) ), atom )
      case ReflexivityAxiom( term ) => Reflexivity( labels( Suc( 0 ) ), term )
      case TopAxiom                 => TopRight( labels( Suc( 0 ) ) )
      case BottomAxiom              => BottomLeft( labels( Ant( 0 ) ) )
      case lk.TheoryAxiom( seq )    => lkskNew.TheoryAxiom( labels zip seq )

      case p @ ContractionLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        ContractionLeft( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux1, aux2 )
      case p @ ContractionRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        ContractionRight( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux1, aux2 )

      case p @ WeakeningLeftRule( subProof, formula ) =>
        WeakeningLeft(
          apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ),
          labels( p.mainIndices.head ) -> formula
        )
      case p @ WeakeningRightRule( subProof, formula ) =>
        WeakeningRight(
          apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ),
          labels( p.mainIndices.head ) -> formula
        )

      case p @ NegLeftRule( subProof, aux: Suc ) =>
        NegLeft( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux )
      case p @ NegRightRule( subProof, aux: Ant ) =>
        NegRight( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux )

      case p @ AndLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        AndLeft( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux1, aux2 )
      case p @ AndRightRule( subProof1, aux1: Suc, subProof2, aux2: Suc ) =>
        AndRight( apply( subProof1, p.getLeftOccConnector.parent( labels ), p.getLeftOccConnector.parent( isCutAnc ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parent( labels ), p.getRightOccConnector.parent( isCutAnc ) ), aux2 )

      case p @ OrLeftRule( subProof1, aux1: Ant, subProof2, aux2: Ant ) =>
        OrLeft( apply( subProof1, p.getLeftOccConnector.parent( labels ), p.getLeftOccConnector.parent( isCutAnc ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parent( labels ), p.getRightOccConnector.parent( isCutAnc ) ), aux2 )
      case p @ OrRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        OrRight( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux1, aux2 )

      case p @ ImpLeftRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        ImpLeft( apply( subProof1, p.getLeftOccConnector.parent( labels ), p.getLeftOccConnector.parent( isCutAnc ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parent( labels ), p.getRightOccConnector.parent( isCutAnc ) ), aux2 )
      case p @ ImpRightRule( subProof, aux1: Ant, aux2: Suc ) =>
        ImpRight( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux1, aux2 )

      case p @ CutRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        Cut(
          apply( subProof1, p.getLeftOccConnector.parent( labels, Seq() ), p.getLeftOccConnector.parent( isCutAnc, true ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parent( labels, Seq() ), p.getRightOccConnector.parent( isCutAnc, true ) ), aux2
        )

      case p: EqualityRule =>
        val lambdaPos = HOLPosition.toLambdaPosition( p.auxFormula )( p.pos )
        Equality(
          apply( p.subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ),
          p.eq.asInstanceOf[Ant], p.aux, p.leftToRight, lambdaPos
        )

      case p @ ForallLeftRule( subProof, aux: Ant, formula, term, v ) if !isCutAnc( p.mainIndices.head ) =>
        AllSkLeft(
          apply( subProof, p.getOccConnector.parent( labels ).updated( aux, labels( p.mainIndices.head ) :+ term ), p.getOccConnector.parent( isCutAnc ) ),
          aux, All( v, formula ), term
        )
      case p @ ExistsRightRule( subProof, aux: Suc, formula, term, v ) if !isCutAnc( p.mainIndices.head ) =>
        ExSkRight(
          apply( subProof, p.getOccConnector.parent( labels ).updated( aux, labels( p.mainIndices.head ) :+ term ), p.getOccConnector.parent( isCutAnc ) ),
          aux, Ex( v, formula ), term
        )
      case p @ ForallLeftRule( subProof, aux: Ant, formula, term, v ) if isCutAnc( p.mainIndices.head ) =>
        AllLeft(
          apply( subProof, p.getOccConnector.parent( labels ).updated( aux, labels( p.mainIndices.head ) :+ term ), p.getOccConnector.parent( isCutAnc ) ),
          aux, All( v, formula ), term
        )
      case p @ ExistsRightRule( subProof, aux: Suc, formula, term, v ) if isCutAnc( p.mainIndices.head ) =>
        ExRight(
          apply( subProof, p.getOccConnector.parent( labels ).updated( aux, labels( p.mainIndices.head ) :+ term ), p.getOccConnector.parent( isCutAnc ) ),
          aux, Ex( v, formula ), term
        )

      case p @ ForallRightRule( subProof, aux: Suc, eigen, quant ) if !isCutAnc( p.mainIndices.head ) =>
        val ls = labels( p.mainIndices.head )
        val skolemSymbol = Const( skolemSymbolFactory.getSkolemSymbol, FunctionType( eigen.exptype, ls.map( _.exptype ) ) )
        val subProof_ = applySubstitution( Substitution( eigen -> skolemSymbol( ls: _* ) ) )( subProof )
        AllSkRight( apply( subProof_, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux, p.mainFormula, skolemSymbol )
      case p @ ExistsLeftRule( subProof, aux: Ant, eigen, quant ) if !isCutAnc( p.mainIndices.head ) =>
        val ls = labels( p.mainIndices.head )
        val skolemSymbol = Const( skolemSymbolFactory.getSkolemSymbol, FunctionType( eigen.exptype, ls.map( _.exptype ) ) )
        val subProof_ = applySubstitution( Substitution( eigen -> skolemSymbol( ls: _* ) ) )( subProof )
        ExSkLeft( apply( subProof_, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux, p.mainFormula, skolemSymbol )

      case p @ ForallRightRule( subProof, aux: Suc, eigen, quant ) if isCutAnc( p.mainIndices.head ) =>
        AllRight( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux, p.mainFormula, eigen )
      case p @ ExistsLeftRule( subProof, aux: Ant, eigen, quant ) if isCutAnc( p.mainIndices.head ) =>
        ExLeft( apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ) ), aux, p.mainFormula, eigen )
    }
    require( res.labels == labels, s"${res.labels} == $labels" )
    res
  }
}

object LKToLKsk {
  def apply( p: LKProof ): LKskProof = ( new LKToLKsk( new SkolemSymbolFactory ) )( p )
}
