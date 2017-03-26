package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.SkolemSymbolFactory
import at.logic.gapt.proofs.{ Ant, HOLSequent, Sequent }
import at.logic.gapt.utils.StreamUtils
import StreamUtils._

object skolemize {
  def apply( formula: Formula, pol: Polarity, context: Seq[Expr], skolemSymbols: Stream[String] ): Formula = formula match {
    case Bottom() | Top() | Atom( _, _ ) =>
      formula
    case Neg( f )                => Neg( skolemize( f, !pol, context, skolemSymbols ) )
    case And( l, r )             => And( skolemize( l, pol, context, even( skolemSymbols ) ), skolemize( r, pol, context, odd( skolemSymbols ) ) )
    case Or( l, r )              => Or( skolemize( l, pol, context, even( skolemSymbols ) ), skolemize( r, pol, context, odd( skolemSymbols ) ) )
    case Imp( l, r )             => Imp( skolemize( l, !pol, context, even( skolemSymbols ) ), skolemize( r, pol, context, odd( skolemSymbols ) ) )
    case Ex( x, f ) if pol.inSuc => Ex( x, skolemize( f, pol, context :+ x, skolemSymbols ) )
    case Ex( x, f ) if pol.inAnt =>
      val sym = Const( skolemSymbols.head, FunctionType( x.ty, context.map( _.ty ) ) )
      val skolemFunction = sym( context: _* )
      skolemize( Substitution( x -> skolemFunction )( f ), pol, context, skolemSymbols.tail )
    case All( x, f ) if pol.inAnt => All( x, skolemize( f, pol, context :+ x, skolemSymbols ) )
    case All( x, f ) if pol.inSuc => skolemize( Ex( x, -f ), !pol, context, skolemSymbols ) match { case Neg( f_ ) => f_ }
  }

  def apply( formula: Formula, pol: Polarity ): Formula =
    apply( formula, pol, Seq(), new SkolemSymbolFactory( constants( formula ) ).getSkolemSymbols )

  def apply( formula: Formula ): Formula =
    apply( formula, Polarity.InSuccedent )

  def apply( sequent: HOLSequent ): HOLSequent = {
    val factory = rename.awayFrom( containedNames( sequent ) )
    for ( ( f, i ) <- sequent.zipWithIndex )
      yield apply( f, i.polarity, Seq(), factory.freshStream( "s" ) )
  }

  private def maybeSkolemize( formula: Formula, pol: Polarity, contextAndSymbols: Option[( Seq[Expr], Stream[String] )] ): Formula =
    contextAndSymbols match {
      case Some( ( context, skolemSymbols ) ) => skolemize( formula, pol, context, skolemSymbols )
      case None                               => formula
    }

  def apply( proof: LKProof ): LKProof = {
    val factory = new SkolemSymbolFactory( proof.subProofs flatMap { _.conclusion.elements } flatMap { constants( _ ) } )
    val contextAndSymbols = proof.endSequent.map { _ => Some( Seq() -> factory.getSkolemSymbols ) }
    cleanStructuralRules( apply( proof, contextAndSymbols ) )
  }

  def apply( proof: LKProof, contextAndSymbols: Sequent[Option[( Seq[Expr], Stream[String] )]] ): LKProof = proof match {
    // Initial sequents are already skolemized
    case InitialSequent( _ ) => proof

    // Structural rules:
    // Here we only need to copy contextAndSymbols correctly
    case proof @ WeakeningLeftRule( subProof, formula ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      WeakeningLeftRule( subProof_, maybeSkolemize( formula, Polarity.InAntecedent, contextAndSymbols( proof.mainIndices.head ) ) )
    case proof @ WeakeningRightRule( subProof, formula ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      WeakeningRightRule( subProof_, maybeSkolemize( formula, Polarity.InSuccedent, contextAndSymbols( proof.mainIndices.head ) ) )
    case proof @ ContractionLeftRule( subProof, aux1, aux2 ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      ContractionLeftRule( subProof_, aux1, aux2 )
    case proof @ ContractionRightRule( subProof, aux1, aux2 ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      ContractionRightRule( subProof_, aux1, aux2 )
    case proof @ CutRule( subProof1, aux1, subProof2, aux2 ) =>
      val subProof1_ = apply( subProof1, proof.getLeftSequentConnector.parents( contextAndSymbols ).map( _.headOption.flatten ) )
      val subProof2_ = apply( subProof2, proof.getRightSequentConnector.parents( contextAndSymbols ).map( _.headOption.flatten ) )
      CutRule( subProof1_, aux1, subProof2_, aux2 )

    // Propositional rules (non-nullary):
    // Here we need to do the mimick the way we assigned skolem symbols in formulas.
    case proof @ NegLeftRule( subProof, aux ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      NegLeftRule( subProof_, aux )
    case proof @ NegRightRule( subProof, aux ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      NegRightRule( subProof_, aux )
    case proof @ AndLeftRule( subProof, aux1, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      AndLeftRule( subProof_, aux1, aux2 )
    case proof @ AndRightRule( subProof1, aux1, subProof2, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof1_ = apply( subProof1, proof.getLeftSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
      val subProof2_ = apply( subProof2, proof.getRightSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      AndRightRule( subProof1_, aux1, subProof2_, aux2 )
    case proof @ OrLeftRule( subProof1, aux1, subProof2, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof1_ = apply( subProof1, proof.getLeftSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
      val subProof2_ = apply( subProof2, proof.getRightSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      OrLeftRule( subProof1_, aux1, subProof2_, aux2 )
    case proof @ OrRightRule( subProof, aux1, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      OrRightRule( subProof_, aux1, aux2 )
    case proof @ ImpLeftRule( subProof1, aux1, subProof2, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof1_ = apply( subProof1, proof.getLeftSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } ) )
      val subProof2_ = apply( subProof2, proof.getRightSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      ImpLeftRule( subProof1_, aux1, subProof2_, aux2 )
    case proof @ ImpRightRule( subProof, aux1, aux2 ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux1, ctxAndSym map { case ( context, symbols ) => context -> even( symbols ) } )
        .updated( aux2, ctxAndSym map { case ( context, symbols ) => context -> odd( symbols ) } ) )
      ImpRightRule( subProof_, aux1, aux2 )

    // Equality rules:
    // Luckily, Skolemization changes neither the indices nor the term positions, so we can keep them.
    case proof @ EqualityLeftRule( subProof, eq, aux, con ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      EqualityLeftRule( subProof_, eq, aux, con )
    case proof @ EqualityRightRule( subProof, eq, aux, con ) =>
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
      EqualityRightRule( subProof_, eq, aux, con )

    // Weak quantifier rules:
    case proof @ ForallLeftRule( subProof, aux, matrix, term, v ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux, ctxAndSym map { case ( context, symbols ) => ( context :+ term ) -> symbols } ) )
      val All( v_, matrix_ ) = maybeSkolemize( proof.mainFormula, Polarity.InAntecedent, ctxAndSym )
      ForallLeftRule( subProof_, aux, matrix_, term, v )
    case proof @ ExistsRightRule( subProof, aux, matrix, term, v ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux, ctxAndSym map { case ( context, symbols ) => ( context :+ term ) -> symbols } ) )
      val Ex( v_, matrix_ ) = maybeSkolemize( proof.mainFormula, Polarity.InSuccedent, ctxAndSym )
      ExistsRightRule( subProof_, aux, matrix_, term, v )

    // Strong quantifier rules:
    case proof @ ExistsLeftRule( subProof, aux, eigen, quant ) =>
      contextAndSymbols( proof.mainIndices.head ) match {
        case Some( ( context, skolemSymbols ) ) =>
          val sym = Const( skolemSymbols.head, FunctionType( eigen.ty, context.map( _.ty ) ) )
          val skolemFunction = sym( context: _* )
          val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
            .updated( aux, Some( context -> skolemSymbols.tail ) ) )
          ExchangeLeftMacroRule( Substitution( eigen -> skolemFunction )( subProof_ ), aux )
        case None =>
          val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
          ExistsLeftRule( subProof_, aux, eigen, quant )
      }
    case proof @ ForallRightRule( subProof, aux, eigen, quant ) =>
      contextAndSymbols( proof.mainIndices.head ) match {
        case Some( ( context, skolemSymbols ) ) =>
          val sym = Const( skolemSymbols.head, FunctionType( eigen.ty, context.map( _.ty ) ) )
          val skolemFunction = sym( context: _* )
          val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
            .updated( aux, Some( context -> skolemSymbols.tail ) ) )
          ExchangeRightMacroRule( Substitution( eigen -> skolemFunction )( subProof_ ), aux )
        case None =>
          val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head ) )
          ForallRightRule( subProof_, aux, eigen, quant )
      }
  }
}