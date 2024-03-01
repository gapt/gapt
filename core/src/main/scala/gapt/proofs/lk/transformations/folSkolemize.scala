package gapt.proofs.lk.transformations

import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.containedNames
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.util.constants
import gapt.expr.util.rename
import gapt.logic.Polarity
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKProofSubstitutableDefault
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.ExchangeLeftMacroRule
import gapt.proofs.lk.rules.macros.ExchangeRightMacroRule
import gapt.utils.NameGenerator
import gapt.utils.StreamUtils.odd
import gapt.utils.StreamUtils.even

object folSkolemize {
  private[lk] class SkolemSymbolFactory( usedConstants: Iterable[Const] ) {
    private var skolem_symbol_stream = new NameGenerator( usedConstants map { _.name } ).freshStream( "s" )

    def getSkolemSymbols: LazyList[String] = {
      val stream = even( skolem_symbol_stream )
      skolem_symbol_stream = odd( skolem_symbol_stream )
      stream
    }

    def getSkolemSymbol: String = {
      val sym = skolem_symbol_stream.head
      skolem_symbol_stream = skolem_symbol_stream.tail
      sym
    }
  }

  def apply( formula: Formula, pol: Polarity, context: Seq[Expr], skolemSymbols: LazyList[String] ): Formula = formula match {
    case Bottom() | Top() | Atom( _, _ ) =>
      formula
    case Neg( f )                => Neg( folSkolemize( f, !pol, context, skolemSymbols ) )
    case And( l, r )             => And( folSkolemize( l, pol, context, even( skolemSymbols ) ), folSkolemize( r, pol, context, odd( skolemSymbols ) ) )
    case Or( l, r )              => Or( folSkolemize( l, pol, context, even( skolemSymbols ) ), folSkolemize( r, pol, context, odd( skolemSymbols ) ) )
    case Imp( l, r )             => Imp( folSkolemize( l, !pol, context, even( skolemSymbols ) ), folSkolemize( r, pol, context, odd( skolemSymbols ) ) )
    case Ex( x, f ) if pol.inSuc => Ex( x, folSkolemize( f, pol, context :+ x, skolemSymbols ) )
    case Ex( x, f ) if pol.inAnt =>
      val sym = Const( skolemSymbols.head, FunctionType( x.ty, context.map( _.ty ) ) )
      val skolemFunction = sym( context: _* )
      folSkolemize( Substitution( x -> skolemFunction )( f ), pol, context, skolemSymbols.tail )
    case All( x, f ) if pol.inAnt => All( x, folSkolemize( f, pol, context :+ x, skolemSymbols ) )
    case All( x, f ) if pol.inSuc => folSkolemize( Ex( x, -f ), !pol, context, skolemSymbols ) match { case Neg( f_ ) => f_ }
  }

  def apply( formula: Formula, pol: Polarity ): Formula =
    apply( formula, pol, Seq(), new SkolemSymbolFactory( constants.nonLogical( formula ) ).getSkolemSymbols )

  def apply( formula: Formula ): Formula =
    apply( formula, Polarity.InSuccedent )

  def apply( sequent: HOLSequent ): HOLSequent = {
    val factory = rename.awayFrom( containedNames( sequent ) )
    for ( ( f, i ) <- sequent.zipWithIndex )
      yield apply( f, i.polarity, Seq(), factory.freshStream( "s" ) )
  }

  private def maybeSkolemize( formula: Formula, pol: Polarity, contextAndSymbols: Option[( Seq[Expr], LazyList[String] )] ): Formula =
    contextAndSymbols match {
      case Some( ( context, skolemSymbols ) ) => folSkolemize( formula, pol, context, skolemSymbols )
      case None                               => formula
    }

  def apply( proof: LKProof ): LKProof = {
    val factory = new SkolemSymbolFactory( proof.subProofs flatMap { _.conclusion.elements } flatMap { constants.nonLogical( _ ) } )
    val contextAndSymbols = proof.endSequent.map { _ => Some( Seq() -> factory.getSkolemSymbols ) }
    cleanStructuralRules( apply( proof, contextAndSymbols ) )
  }

  def apply( proof: LKProof, contextAndSymbols: Sequent[Option[( Seq[Expr], LazyList[String] )]] ): LKProof = proof match {
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
      val All( v_, matrix_ ) = maybeSkolemize( proof.mainFormula, Polarity.InAntecedent, ctxAndSym ): @unchecked
      ForallLeftRule( subProof_, aux, matrix_, term, v )
    case proof @ ExistsRightRule( subProof, aux, matrix, term, v ) =>
      val ctxAndSym = contextAndSymbols( proof.mainIndices.head )
      val subProof_ = apply( subProof, proof.getSequentConnector.parents( contextAndSymbols ).map( _.head )
        .updated( aux, ctxAndSym map { case ( context, symbols ) => ( context :+ term ) -> symbols } ) )
      val Ex( v_, matrix_ ) = maybeSkolemize( proof.mainFormula, Polarity.InSuccedent, ctxAndSym ): @unchecked
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
