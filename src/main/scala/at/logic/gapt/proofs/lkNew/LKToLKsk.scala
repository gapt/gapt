package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, SkolemSymbolFactory }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkskNew.LKskProof._
import at.logic.gapt.proofs.lkskNew
import at.logic.gapt.proofs.lkskNew._

object LKToLKsk {
  def apply( p: LKProof ): LKskProof = apply( p, p.conclusion map { _ => Seq() } )

  def apply( p: LKProof, labels: Sequent[Label] ): LKskProof = {
    val res = p match {
      case LogicalAxiom( atom )     => lkskNew.Axiom( labels( Ant( 0 ) ), labels( Suc( 0 ) ), atom )
      case ReflexivityAxiom( term ) => Reflexivity( labels( Suc( 0 ) ), term )
      case TopAxiom                 => TopRight( labels( Suc( 0 ) ) )
      case BottomAxiom              => BottomLeft( labels( Ant( 0 ) ) )

      case p @ ContractionLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        ContractionLeft( apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ), aux1, aux2 )
      case p @ ContractionRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        ContractionRight( apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ), aux1, aux2 )

      case p @ WeakeningLeftRule( subProof, formula ) =>
        WeakeningLeft(
          apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ),
          labels( p.mainIndices.head ) -> formula
        )
      case p @ WeakeningRightRule( subProof, formula ) =>
        WeakeningRight(
          apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ),
          labels( p.mainIndices.head ) -> formula
        )

      case p @ NegLeftRule( subProof, aux: Suc ) =>
        NegLeft( apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ), aux )
      case p @ NegRightRule( subProof, aux: Ant ) =>
        NegRight( apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ), aux )

      case p @ AndLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        AndLeft( apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ), aux1, aux2 )
      case p @ AndRightRule( subProof1, aux1: Suc, subProof2, aux2: Suc ) =>
        AndRight( apply( subProof1, p.getLeftOccConnector.parents( labels ).map( _.head ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parents( labels ).map( _.head ) ), aux2 )

      case p @ OrLeftRule( subProof1, aux1: Ant, subProof2, aux2: Ant ) =>
        OrLeft( apply( subProof1, p.getLeftOccConnector.parents( labels ).map( _.head ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parents( labels ).map( _.head ) ), aux2 )
      case p @ OrRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        OrRight( apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ), aux1, aux2 )

      case p @ ImpLeftRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        ImpLeft( apply( subProof1, p.getLeftOccConnector.parents( labels ).map( _.head ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parents( labels ).map( _.head ) ), aux2 )
      case p @ ImpRightRule( subProof, aux1: Ant, aux2: Suc ) =>
        ImpRight( apply( subProof, p.getOccConnector.parents( labels ).map( _.head ) ), aux1, aux2 )

      case p @ CutRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        Cut(
          apply( subProof1, p.getLeftOccConnector.parents( labels ).updated( aux1, Seq( Seq() ) ).map( _.head ) ), aux1,
          apply( subProof2, p.getRightOccConnector.parents( labels ).updated( aux2, Seq( Seq() ) ).map( _.head ) ), aux2
        )

      case p: EqualityRule =>
        val lambdaPos = HOLPosition.toLambdaPosition( p.auxFormula )( p.pos )
        Equality(
          apply( p.subProof, p.getOccConnector.parents( labels ).map( _.head ) ),
          p.eq.asInstanceOf[Ant], p.aux, p.leftToRight, lambdaPos
        )

      case p @ ForallLeftRule( subProof, aux: Ant, formula, term, v ) =>
        AllLeft(
          apply( subProof, p.getOccConnector.parents( labels ).map( _.head ).updated( aux, labels( p.mainIndices.head ) :+ term ) ),
          aux, All( v, formula ), term
        )
      case p @ ExistsRightRule( subProof, aux: Suc, formula, term, v ) =>
        ExRight(
          apply( subProof, p.getOccConnector.parents( labels ).map( _.head ).updated( aux, labels( p.mainIndices.head ) :+ term ) ),
          aux, Ex( v, formula ), term
        )

      case p @ ForallRightRule( subProof, aux: Suc, eigen, quant ) =>
        val ls = labels( p.mainIndices.head )
        val skolemSymbol = Const( SkolemSymbolFactory.getSkolemSymbol, FunctionType( eigen.exptype, ls.map( _.exptype ) ) )
        val subProof_ = applySubstitution( Substitution( eigen -> skolemSymbol( ls: _* ) ) )( subProof )
        AllRight( apply( subProof_, p.getOccConnector.parents( labels ).map( _.head ) ), aux, p.mainFormula, skolemSymbol )
      case p @ ExistsLeftRule( subProof, aux: Ant, eigen, quant ) =>
        val ls = labels( p.mainIndices.head )
        val skolemSymbol = Const( SkolemSymbolFactory.getSkolemSymbol, FunctionType( eigen.exptype, ls.map( _.exptype ) ) )
        val subProof_ = applySubstitution( Substitution( eigen -> skolemSymbol( ls: _* ) ) )( subProof )
        ExLeft( apply( subProof_, p.getOccConnector.parents( labels ).map( _.head ) ), aux, p.mainFormula, skolemSymbol )
    }
    require( res.labels == labels, s"${res.labels} == $labels" )
    res
  }
}
