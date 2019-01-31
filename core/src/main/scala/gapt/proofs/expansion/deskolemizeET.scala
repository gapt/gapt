package gapt.proofs.expansion

import gapt.expr._
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.transformations.LKToExpansionProof

/**
 * Deskolemization of expansion trees.
 *
 * We first gather the skolem terms in a given [[ExpansionProof]] from the [[ETSkolemQuantifier]]s.
 * Then replace each [[ETSkolemQuantifier]] by [[ETStrongQuantifier]], and each skolem term within, by a fresh eigenvariable.
 */
object deskolemizeET {
  def apply( lkProof: LKProof ): LKProof =
    ExpansionProofToLK( deskolemizeET( LKToExpansionProof( lkProof ) ) ).right.get

  def apply( expansionProof: ExpansionProof, removeCongruences: Boolean = true ): ExpansionProof = {
    val woCongrs = if ( removeCongruences ) removeSkolemCongruences( expansionProof ) else expansionProof
    val skolemsAboveCuts = eliminateMerges( moveSkolemNodesToCuts( woCongrs ) )
    val deskolemized = replaceByEigenvariables( skolemsAboveCuts )
    eliminateCutsET( deskolemized )
  }

  def replaceByEigenvariables( expansionProof: ExpansionProof ): ExpansionProof = {
    val nameGenerator = rename.awayFrom( containedNames( expansionProof ) )
    val skolemTerms = expansionProof.subProofs.collect { case ETSkolemQuantifier( _, skT, _ ) => skT }
    val repl = skolemTerms.map { t => ( t, Var( nameGenerator.fresh( "v" ), t.ty ) ) }.toMap

    ExpansionProof( replace( expansionProof.expansionSequent, repl ) )
  }

  def replace( es: ExpansionSequent, repl: PartialFunction[Expr, Expr] ): ExpansionSequent =
    for ( e <- es ) yield replace( e, repl )

  def replace( et: ExpansionTree, repl: PartialFunction[Expr, Expr] ): ExpansionTree =
    ExpansionTree( TermReplacement( et.shallow, repl ), et.polarity, replace( et.term, repl ) )

  def replace( et: ETt, repl: PartialFunction[Expr, Expr] ): ETt = et match {
    case ETtMerge( child1, child2 ) => ETtMerge( replace( child1, repl ), replace( child2, repl ) )

    case ETtWeakening               => ETtWeakening
    case ETtAtom                    => ETtAtom
    case ETtDef( sh, ch ) =>
      ETtDef( TermReplacement( sh, repl ), replace( ch, repl ) )

    case ETtNullary                  => et
    case ETtUnary( child )           => ETtUnary( replace( child, repl ) )
    case ETtBinary( child1, child2 ) => ETtBinary( replace( child1, repl ), replace( child2, repl ) )

    case ETtWeak( instances ) =>
      ETtWeak.withMerge(
        instances.map {
          case ( selectedTerm, child ) =>
            ( TermReplacement( selectedTerm, repl ), replace( child, repl ) )
        } )
    case ETtStrong( eigenVariable, child ) =>
      ETtStrong( TermReplacement( eigenVariable, repl ).asInstanceOf[Var], replace( child, repl ) )
    case ETtSkolem( skolemTerm, child ) =>
      ETtStrong( TermReplacement( skolemTerm, repl ).asInstanceOf[Var], replace( child, repl ) )
  }
}

