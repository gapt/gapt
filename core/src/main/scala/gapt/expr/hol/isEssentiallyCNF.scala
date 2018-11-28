package gapt.expr.hol

import gapt.expr._
import gapt.proofs.HOLSequent

/**
 * Recognizes a class of formulas/sequents including all formulas in
 * clause normal form (i.e., negation of conjunction of clauses).
 *
 * The first-order formulas recognized by this function have the property that
 * they are valid in classical first-order logic if and only if they are valid
 * in intuitionistic first-order logic.
 */
// TODO: cite literature
object isEssentiallyCNF {
  private def hypLhs: Formula => Boolean = {
    case _: Atom     => true
    case Bottom()    => true
    case Top()       => true
    case And( f, g ) => hypLhs( f ) && hypLhs( g )
    case Or( f, g )  => hypLhs( f ) && hypLhs( g )
    case Ex( _, f )  => hypLhs( f )
    case _           => false
  }

  private def hypMatrix: Formula => Boolean = {
    case _: Atom     => true
    case Bottom()    => true
    case Top()       => true
    case All( _, f ) => hypMatrix( f )
    case Imp( f, g ) => hypLhs( f ) && hypMatrix( g )
    case Neg( f )    => hypLhs( f )
    case And( f, g ) => hypMatrix( f ) && hypMatrix( g )
    case Or( f, g )  => hypMatrix( f ) && hypMatrix( g )
    case _           => false
  }

  private def prenexHyp: Formula => Boolean = {
    case All( _, f ) => prenexHyp( f )
    case Ex( _, f )  => prenexHyp( f )
    case And( f, g ) => prenexHyp( f ) && prenexHyp( g )
    case Or( f, g )  => prenexHyp( f ) && prenexHyp( g )
    case f           => hypMatrix( f )
  }

  private def fml: Formula => Boolean = {
    case Imp( f, g ) => prenexHyp( f ) && fml( g )
    case Neg( f )    => prenexHyp( f )
    case And( f, g ) => fml( f ) && fml( g )
    case All( _, f ) => fml( f )
    case f           => hypLhs( f )
  }

  def apply( formula: Formula ): Boolean = fml( formula )
  def apply( sequent: HOLSequent ): Boolean = apply( sequent.toImplication )
}
