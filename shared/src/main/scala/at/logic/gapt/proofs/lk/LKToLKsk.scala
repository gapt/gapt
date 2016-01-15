package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, SkolemSymbolFactory }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkskNew._
import at.logic.gapt.utils.ds.streams.Definitions._

object LKToLKsk {
  def apply( proof: LKProof ): LKskProof = {
    val factory = new SkolemSymbolFactory
    val contextAndSymbols = proof.endSequent.map { _ => Some( Seq() -> factory.getSkolemSymbols ) }
    apply( proof, contextAndSymbols )
  }

  def apply( proof: LKProof, contextAndSymbols: Sequent[Option[( Seq[LambdaExpression], Stream[SymbolA] )]] ): LKskProof = {
    val labels = contextAndSymbols.map { _.map { _._1 }.getOrElse( Seq() ) }
    proof match {
      // Initial sequents are already skolemized
      case LogicalAxiom( atom )     => lkskNew.Axiom( labels( Ant( 0 ) ), labels( Suc( 0 ) ), atom )
      case ReflexivityAxiom( term ) => Reflexivity( labels( Suc( 0 ) ), term )
      case TopAxiom                 => TopRight( labels( Suc( 0 ) ) )
      case BottomAxiom              => BottomLeft( labels( Ant( 0 ) ) )
      case lk.TheoryAxiom( seq )    => lkskNew.TheoryAxiom( labels zip seq )

      // Structural rules:
      // Here we only need to copy contextAndSymbols correctly
      case proof @ WeakeningLeftRule( subProof, formula ) =>
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        WeakeningLeft( subProof_, labels( proof.mainIndices.head ) -> formula )
      case proof @ WeakeningRightRule( subProof, formula ) =>
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        WeakeningRight( subProof_, labels( proof.mainIndices.head ) -> formula )
      case proof @ ContractionLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        ContractionLeft( subProof_, aux1, aux2 )
      case proof @ ContractionRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        ContractionRight( subProof_, aux1, aux2 )
      case proof @ CutRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.headOption.flatten ) )
        val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.headOption.flatten ) )
        Cut( subProof1_, aux1, subProof2_, aux2 )

      // Propositional rules (non-nullary):
      // Here we need to do the mimick the way we assigned skolem symbols in formulas.
      case proof @ NegLeftRule( subProof, aux: Suc ) =>
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        NegLeft( subProof_, aux )
      case proof @ NegRightRule( subProof, aux: Ant ) =>
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        NegRight( subProof_, aux )
      case proof @ AndLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
          .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
        AndLeft( subProof_, aux1, aux2 )
      case proof @ AndRightRule( subProof1, aux1: Suc, subProof2, aux2: Suc ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
        val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
        AndRight( subProof1_, aux1, subProof2_, aux2 )
      case proof @ OrLeftRule( subProof1, aux1: Ant, subProof2, aux2: Ant ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
        val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
        OrLeft( subProof1_, aux1, subProof2_, aux2 )
      case proof @ OrRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
          .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
        OrRight( subProof_, aux1, aux2 )
      case proof @ ImpLeftRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
        val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
        ImpLeft( subProof1_, aux1, subProof2_, aux2 )
      case proof @ ImpRightRule( subProof, aux1: Ant, aux2: Suc ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
          .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
        ImpRight( subProof_, aux1, aux2 )

      // Equality rules:
      // Luckily, LKsk has the same indices and the term positions, so we can keep them.
      case proof @ EqualityLeftRule( subProof, eq: Ant, aux, pos ) =>
        val lambdaPos = pos map { HOLPosition.toLambdaPosition( proof.auxFormula ) }
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        Equality( subProof_, eq, aux, proof.leftToRight, lambdaPos )
      case proof @ EqualityRightRule( subProof, eq: Ant, aux, pos ) =>
        val lambdaPos = pos map { HOLPosition.toLambdaPosition( proof.auxFormula ) }
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
        Equality( subProof_, eq, aux, proof.leftToRight, lambdaPos )

      // Weak quantifier rules:
      case proof @ ForallLeftRule( subProof, aux: Ant, matrix, term, v ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux, ctxAndSym map { case ( context, symbols ) => ( context :+ term ) -> symbols } ) )
        if ( ctxAndSym.isDefined )
          AllSkLeft( subProof_, aux, proof.mainFormula, term )
        else
          AllLeft( subProof_, aux, proof.mainFormula, term )
      case proof @ ExistsRightRule( subProof, aux: Suc, matrix, term, v ) =>
        val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
        val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
          .updated( aux, ctxAndSym map { case ( context, symbols ) => ( context :+ term ) -> symbols } ) )
        if ( ctxAndSym.isDefined )
          ExSkRight( subProof_, aux, proof.mainFormula, term )
        else
          ExRight( subProof_, aux, proof.mainFormula, term )

      // Strong quantifier rules:
      case proof @ ExistsLeftRule( subProof, aux: Ant, eigen, quant ) =>
        contextAndSymbols( proof.mainIndices.head ) match {
          case Some( ( context, skolemSymbols ) ) =>
            val sym = Const( skolemSymbols.head, FunctionType( eigen.exptype, context.map( _.exptype ) ) )
            val skolemFunction = sym( context: _* )
            val subProof_ = apply(
              applySubstitution( Substitution( eigen -> skolemFunction ) )( subProof ),
              proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
                .updated( aux, Some( context -> skolemSymbols.tail ) )
            )
            ExSkLeft( subProof_, aux, proof.mainFormula, sym )
          case None =>
            val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
            ExLeft( subProof_, aux, proof.mainFormula, eigen )
        }
      case proof @ ForallRightRule( subProof, aux: Suc, eigen, quant ) =>
        contextAndSymbols( proof.mainIndices.head ) match {
          case Some( ( context, skolemSymbols ) ) =>
            val sym = Const( skolemSymbols.head, FunctionType( eigen.exptype, context.map( _.exptype ) ) )
            val skolemFunction = sym( context: _* )
            val subProof_ = apply(
              applySubstitution( Substitution( eigen -> skolemFunction ) )( subProof ),
              proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
                .updated( aux, Some( context -> skolemSymbols.tail ) )
            )
            AllSkRight( subProof_, aux, proof.mainFormula, sym )
          case None =>
            val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
            AllRight( subProof_, aux, proof.mainFormula, eigen )
        }
    }
  }
}
