package at.logic.gapt.proofs.expansion
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable

object tautAtomicExpansionET {
  import Polarity._
  def apply( formula: Formula )( implicit nameGen: NameGenerator ): ( ExpansionTree, ExpansionTree ) =
    formula match {
      case Top()    => ETTop( InAntecedent ) -> ETTop( InSuccedent )
      case Bottom() => ETBottom( InAntecedent ) -> ETBottom( InSuccedent )
      case Neg( f ) =>
        val ( f1, f2 ) = apply( f )
        ETNeg( f2 ) -> ETNeg( f1 )
      case And( f, g ) =>
        val ( f1, f2 ) = apply( f )
        val ( g1, g2 ) = apply( g )
        ETAnd( f1, g1 ) -> ETAnd( f2, g2 )
      case Or( f, g ) =>
        val ( f1, f2 ) = apply( f )
        val ( g1, g2 ) = apply( g )
        ETOr( f1, g1 ) -> ETOr( f2, g2 )
      case Imp( f, g ) =>
        val ( f1, f2 ) = apply( f )
        val ( g1, g2 ) = apply( g )
        ETImp( f2, g1 ) -> ETImp( f1, g2 )
      case All( x0, _ ) =>
        val x = nameGen.fresh( x0 )
        val ( f1, f2 ) = apply( instantiate( formula, x ) )
        ETWeakQuantifier( formula, Map( x -> f1 ) ) -> ETStrongQuantifier( formula, x, f2 )
      case Ex( x0, _ ) =>
        val x = nameGen.fresh( x0 )
        val ( f1, f2 ) = apply( instantiate( formula, x ) )
        ETStrongQuantifier( formula, x, f1 ) -> ETWeakQuantifier( formula, Map( x -> f2 ) )
      case atom: Atom => ETAtom( atom, InAntecedent ) -> ETAtom( atom, InSuccedent )
    }
}

object moveSkolemNodesToCuts {

  def apply( ep: ExpansionProof ): ExpansionProof = {
    implicit val nameGen: NameGenerator = rename.awayFrom( ep.eigenVariables ++ freeVariablesET( ep ) )
    val cuts = mutable.Buffer[ETImp]()
    val es = ep.expansionSequent.map( apply( _, cuts ) )
    ExpansionProof( ETCut( cuts ) +: es )
  }

  def apply( et: ExpansionTree, cuts: mutable.Buffer[ETImp] )( implicit nameGen: NameGenerator ): ExpansionTree =
    et match {
      case _: ETWeakening | _: ETBottom | _: ETTop | _: ETAtom => et
      case ETNeg( f ) => ETNeg( apply( f, cuts ) )
      case ETAnd( f, g ) => ETAnd( apply( f, cuts ), apply( g, cuts ) )
      case ETOr( f, g ) => ETOr( apply( f, cuts ), apply( g, cuts ) )
      case ETImp( f, g ) => ETImp( apply( f, cuts ), apply( g, cuts ) )
      case ETDefinition( sh, f ) => ETDefinition( sh, apply( f, cuts ) )
      case ETMerge( f, g ) => ETMerge( apply( f, cuts ), apply( g, cuts ) )
      case ETWeakQuantifier( sh, insts ) =>
        ETWeakQuantifier( sh, for ( ( t, f ) <- insts ) yield t -> apply( f, cuts ) )
      case ETStrongQuantifier( sh, ev, f ) =>
        ETStrongQuantifier( sh, ev, apply( f, cuts ) )
      case ETSkolemQuantifier( sh, t, d, f ) if et.polarity.inSuc =>
        val ( a, b ) = tautAtomicExpansionET( sh )
        cuts += ETImp( ETSkolemQuantifier( sh, t, d, apply( f, cuts ) ), a )
        b
      case ETSkolemQuantifier( sh, t, d, f ) if et.polarity.inAnt =>
        val ( a, b ) = tautAtomicExpansionET( sh )
        cuts += ETImp( b, ETSkolemQuantifier( sh, t, d, apply( f, cuts ) ) )
        a
    }

}
