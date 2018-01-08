package at.logic.gapt.proofs.epsilon2

import at.logic.gapt.proofs.{ Context, MutableContext }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate

object EpsilonToExpansionProof {

  def apply( cf: CriticalFormula )( implicit ctx: Context ): ExpansionTree = {
    val Some( skDef @ Abs.Block( vs, quant @ Quant( _, _, isAll ) ) ) = ctx.skolemDef( cf.skSym )
    val polWithSk = if ( isAll ) Polarity.Positive else Polarity.Negative
    val cutf = Substitution( vs zip cf.skArgs )( quant )
    val formulaWithSk =
      ETSkolemQuantifier( cutf, cf.skTerm, skDef,
        formulaToExpansionTree( instantiate( cutf, cf.skTerm ), polWithSk ) )
    val formulaWithTerm =
      ETWeakQuantifier( cutf, Map( cf.term ->
        formulaToExpansionTree( instantiate( cutf, cf.term ), !polWithSk ) ) )
    if ( isAll ) ETCut( formulaWithSk, formulaWithTerm ) else ETCut( formulaWithTerm, formulaWithSk )
  }

  def apply( sh: Formula, eps: Formula, pol: Polarity )( implicit ctx: Context ): ExpansionTree =
    ( sh, eps ) match {
      case ( Top(), Top() )                       => ETTop( pol )
      case ( Bottom(), Bottom() )                 => ETBottom( pol )
      case ( sh: Atom, eps: Atom )                => ETAtom( sh, pol )
      case ( Neg( sh1 ), Neg( eps1 ) )            => ETNeg( apply( sh1, eps1, !pol ) )
      case ( And( sh1, sh2 ), And( eps1, eps2 ) ) => ETAnd( apply( sh1, eps1, pol ), apply( sh2, eps2, pol ) )
      case ( Or( sh1, sh2 ), Or( eps1, eps2 ) )   => ETOr( apply( sh1, eps1, pol ), apply( sh2, eps2, pol ) )
      case ( Imp( sh1, sh2 ), Imp( eps1, eps2 ) ) => ETImp( apply( sh1, eps1, !pol ), apply( sh2, eps2, pol ) )
      case ( Quant( x, sub, isAll ), _ ) =>
        val child = apply( sub, eps, pol )
        val Some( subst ) = syntacticMatching( child.deep, eps )
        val Apps( skSym: Const, _ ) = subst( x )

        // TODO: this only works with ε-proofs produced by epsilonize
        val fvs = freeVariables( sh ).toSeq.sortBy( _.name )
        val skDef = Abs.Block( fvs, sh )
        val skTerm = skSym( fvs )

        val shallow = Quant( x, child.shallow, isAll )
        val substChild = Substitution( x -> skTerm )( child )
        if ( isAll == pol.inSuc )
          ETSkolemQuantifier( shallow, skTerm, skDef, substChild )
        else
          ETWeakQuantifier( shallow, Map( skTerm -> substChild ) )
    }

  def patchSkDefs( p: ExpansionProof )( implicit ctx: MutableContext ): ExpansionProof = {
    val repl = for ( ( skC, skD ) <- p.skolemFunctions.skolemDefs )
      yield skC -> ctx.addSkolemSym( skD )
    TermReplacement( p, repl.toMap )
  }

  def apply( p: EpsilonProof )( implicit ctx: MutableContext ): ExpansionProof =
    patchSkDefs( ExpansionProof( p.criticalFormulas.map( apply( _ ) ) ++:
      ( for ( ( ( sh, eps ), i ) <- p.shallow zip p.epsilonized zipWithIndex )
        yield apply( sh, eps, i.polarity ) ) ) )

}
