package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._

/**
 * Deskolemization of expansion trees.
 *
 * We first gather the skolem terms in a given [[ExpansionProof]] from the [[ETSkolemQuantifier]]s.
 * Then replace each [[ETSkolemQuantifier]] by [[ETStrongQuantifier]], and each skolem term within, by a fresh eigenvariable.
 */
object deskolemizeET extends deskolemizeET {
}

class deskolemizeET {

  def apply( expansionProof: ExpansionProof ): ExpansionProof = {

    val nameGenerator = rename.awayFrom( containedNames( expansionProof ) )
    val skolemTerms = expansionProof.subProofs.collect { case e: ETSkolemQuantifier => e.skolemTerm }
    val repl = skolemTerms.map {
      t => ( t, Var( nameGenerator.fresh( "v" ), t.exptype ) )
    }.toMap

    ExpansionProof( apply( expansionProof.expansionSequent, repl ) )
  }

  def apply( es: ExpansionSequent, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionSequent = {
    for { e <- es } yield apply( e, repl )
  }

  def apply( e: ExpansionTree, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionTree = {
    rm( e, repl )
  }

  // TODO unify with replaceET? code is very similar
  def rm( et: ExpansionTree, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionTree = et match {
    case ETMerge( child1, child2 ) => ETMerge( rm( child1, repl ), rm( child2, repl ) )

    case et @ ETWeakening( formula, _ ) =>
      et.copy( formula = TermReplacement( formula, repl ) )
    case et @ ETAtom( atom, _ ) =>
      et.copy( atom = TermReplacement( atom, repl ) )
    case ETDefinition( sh, ch ) =>
      ETDefinition( TermReplacement( sh, repl ), rm( ch, repl ) )

    case _: ETTop | _: ETBottom  => et
    case ETNeg( child )          => ETNeg( rm( child, repl ) )
    case ETAnd( child1, child2 ) => ETAnd( rm( child1, repl ), rm( child2, repl ) )
    case ETOr( child1, child2 )  => ETOr( rm( child1, repl ), rm( child2, repl ) )
    case ETImp( child1, child2 ) => ETImp( rm( child1, repl ), rm( child2, repl ) )

    case ETWeakQuantifier( shallow, instances ) =>
      ETWeakQuantifier.withMerge(
        TermReplacement( shallow, repl ),
        instances.map {
          case ( selectedTerm, child ) =>
            ( TermReplacement( selectedTerm, repl ), rm( child, repl ) )
        }
      )
    case ETStrongQuantifier( shallow, eigenVariable, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( eigenVariable, repl ).asInstanceOf[Var], rm( child, repl )
      )
    case ETSkolemQuantifier( shallow, skolemTerm, skolemDef, child ) =>
      ETStrongQuantifier(
        TermReplacement( shallow, repl ),
        TermReplacement( skolemTerm, repl ).asInstanceOf[Var],
        rm( child, repl )
      )
  }
}

