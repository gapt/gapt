package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.SkolemSymbolFactory
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.utils.ds.streams.Definitions._

object skolemize {
  def apply( formula: HOLFormula, inSuc: Boolean, context: Seq[LambdaExpression], skolemSymbols: Stream[SymbolA] ): HOLFormula = formula match {
    case Bottom() | Top() | HOLAtom( _, _ ) =>
      formula
    case Neg( f )            => Neg( skolemize( f, !inSuc, context, skolemSymbols ) )
    case And( l, r )         => And( skolemize( l, inSuc, context, even( skolemSymbols ) ), skolemize( r, inSuc, context, odd( skolemSymbols ) ) )
    case Or( l, r )          => Or( skolemize( l, inSuc, context, even( skolemSymbols ) ), skolemize( r, inSuc, context, odd( skolemSymbols ) ) )
    case Imp( l, r )         => Imp( skolemize( l, !inSuc, context, even( skolemSymbols ) ), skolemize( r, inSuc, context, odd( skolemSymbols ) ) )
    case Ex( x, f ) if inSuc => Ex( x, skolemize( f, inSuc, context :+ x, skolemSymbols ) )
    case Ex( x, f ) if !inSuc =>
      val sym = Const( skolemSymbols.head, FunctionType( x.exptype, context.map( _.exptype ) ) )
      val skolemFunction = sym( context: _* )
      skolemize( Substitution( x -> skolemFunction )( f ), inSuc, context, skolemSymbols.tail )
    case All( x, f ) if !inSuc => All( x, skolemize( f, inSuc, context :+ x, skolemSymbols ) )
    case All( x, f ) if inSuc  => skolemize( Ex( x, -f ), !inSuc, context, skolemSymbols ) match { case Neg( f_ ) => f_ }
  }

  def apply( formula: HOLFormula, inSuc: Boolean ): HOLFormula =
    apply( formula, inSuc, Seq(), new SkolemSymbolFactory().getSkolemSymbols )

  def apply( formula: HOLFormula ): HOLFormula =
    apply( formula, inSuc = true )

  private def maybeSkolemize( formula: HOLFormula, inSuc: Boolean, contextAndSymbols: Option[( Seq[LambdaExpression], Stream[SymbolA] )] ): HOLFormula =
    contextAndSymbols match {
      case Some( ( context, skolemSymbols ) ) => skolemize( formula, inSuc, context, skolemSymbols )
      case None                               => formula
    }

  def apply( proof: LKProof ): LKProof = {
    val factory = new SkolemSymbolFactory
    val contextAndSymbols = proof.endSequent.map { _ => Some( Seq() -> factory.getSkolemSymbols ) }
    cleanStructuralRules( apply( proof, contextAndSymbols ) )
  }

  def apply( proof: LKProof, contextAndSymbols: Sequent[Option[( Seq[LambdaExpression], Stream[SymbolA] )]] ): LKProof = proof match {
    // Initial sequents are already skolemized
    case InitialSequent( _ ) => proof

    // Structural rules:
    // Here we only need to copy contextAndSymbols correctly
    case proof @ WeakeningLeftRule( subProof, formula ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      WeakeningLeftRule( subProof_, maybeSkolemize( formula, false, contextAndSymbols( proof.mainIndices.head ) ) )
    case proof @ WeakeningRightRule( subProof, formula ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      WeakeningRightRule( subProof_, maybeSkolemize( formula, true, contextAndSymbols( proof.mainIndices.head ) ) )
    case proof @ ContractionLeftRule( subProof, aux1, aux2 ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      ContractionLeftRule( subProof_, aux1, aux2 )
    case proof @ ContractionRightRule( subProof, aux1, aux2 ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      ContractionRightRule( subProof_, aux1, aux2 )
    case proof @ CutRule( subProof1, aux1, subProof2, aux2 ) =>
      val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.headOption.flatten ) )
      val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.headOption.flatten ) )
      CutRule( subProof1_, aux1, subProof2_, aux2 )

    // Propositional rules (non-nullary):
    // Here we need to do the mimick the way we assigned skolem symbols in formulas.
    case proof @ NegLeftRule( subProof, aux ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      NegLeftRule( subProof_, aux )
    case proof @ NegRightRule( subProof, aux ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      NegRightRule( subProof_, aux )
    case proof @ AndLeftRule( subProof, aux1, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      AndLeftRule( subProof_, aux1, aux2 )
    case proof @ AndRightRule( subProof1, aux1, subProof2, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
      val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      AndRightRule( subProof1_, aux1, subProof2_, aux2 )
    case proof @ OrLeftRule( subProof1, aux1, subProof2, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
      val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      OrLeftRule( subProof1_, aux1, subProof2_, aux2 )
    case proof @ OrRightRule( subProof, aux1, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      OrRightRule( subProof_, aux1, aux2 )
    case proof @ ImpLeftRule( subProof1, aux1, subProof2, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof1_ = apply( subProof1, proof.getLeftOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
      val subProof2_ = apply( subProof2, proof.getRightOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      ImpLeftRule( subProof1_, aux1, subProof2_, aux2 )
    case proof @ ImpRightRule( subProof, aux1, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      ImpRightRule( subProof_, aux1, aux2 )

    // Equality rules:
    // Luckily, Skolemization changes neither the indices nor the term positions, so we can keep them.
    case proof @ EqualityLeftRule( subProof, eq, aux, pos ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      EqualityLeftRule( subProof_, eq, aux, pos )
    case proof @ EqualityRightRule( subProof, eq, aux, pos ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      EqualityRightRule( subProof_, eq, aux, pos )

    // Definition rules:
    // We do it as in the old LK: skolemize both the before and after formulas using the same stream of skolem symbols.
    case proof @ DefinitionLeftRule( subProof, aux, main ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      DefinitionLeftRule( subProof_, aux, maybeSkolemize( main, false, contextAndSymbols( proof.mainIndices.head ) ) )
    case proof @ DefinitionRightRule( subProof, aux, main ) =>
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
      DefinitionRightRule( subProof_, aux, maybeSkolemize( main, true, contextAndSymbols( proof.mainIndices.head ) ) )

    // Weak quantifier rules:
    case proof @ ForallLeftRule( subProof, aux, matrix, term, v ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux, ctxAndSym map { case ( context, symbols ) => ( context :+ term ) -> symbols } ) )
      val All( v_, matrix_ ) = maybeSkolemize( proof.mainFormula, false, ctxAndSym )
      ForallLeftRule( subProof_, aux, matrix_, term, v )
    case proof @ ExistsRightRule( subProof, aux, matrix, term, v ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux, ctxAndSym map { case ( context, symbols ) => ( context :+ term ) -> symbols } ) )
      val Ex( v_, matrix_ ) = maybeSkolemize( proof.mainFormula, true, ctxAndSym )
      ExistsRightRule( subProof_, aux, matrix_, term, v )

    // Strong quantifier rules:
    case proof @ ExistsLeftRule( subProof, aux, eigen, quant ) =>
      contextAndSymbols( proof.mainIndices.head ) match {
        case Some( ( context, skolemSymbols ) ) =>
          val sym = Const( skolemSymbols.head, FunctionType( eigen.exptype, context.map( _.exptype ) ) )
          val skolemFunction = sym( context: _* )
          val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
            .updated( aux, Some( context -> skolemSymbols.tail ) ) )
          ExchangeLeftMacroRule( Substitution( eigen -> skolemFunction )( subProof_ ), aux )
        case None =>
          val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
          ExistsLeftRule( subProof_, aux, eigen, quant )
      }
    case proof @ ForallRightRule( subProof, aux, eigen, quant ) =>
      contextAndSymbols( proof.mainIndices.head ) match {
        case Some( ( context, skolemSymbols ) ) =>
          val sym = Const( skolemSymbols.head, FunctionType( eigen.exptype, context.map( _.exptype ) ) )
          val skolemFunction = sym( context: _* )
          val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head )
            .updated( aux, Some( context -> skolemSymbols.tail ) ) )
          ExchangeRightMacroRule( Substitution( eigen -> skolemFunction )( subProof_ ), aux )
        case None =>
          val subProof_ = apply( subProof, proof.getOccConnector.parents( contextAndSymbols ).map( _.head ) )
          ForallRightRule( subProof_, aux, eigen, quant )
      }
  }
}