package gapt.proofs.expansion
import gapt.expr._
import gapt.expr.hol.instantiate
import gapt.utils.NameGenerator

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

object nonProofTheoreticSkolemTerms {
  def apply( ep: ExpansionProof ): Set[Expr] = apply( ep.expansionSequent )
  def apply( es: ExpansionSequent ): Set[Expr] = {
    val occs = mutable.Map[Expr, Set[( List[Expr], List[Int] )]]().withDefaultValue( Set.empty )
    def gatherOccs( et: ExpansionTree, weak: List[Expr], pos: List[Int] ): Unit =
      et match {
        case ETTop( _ ) | ETBottom( _ ) =>
        case ETWeakening( _, _ )        =>
        case ETAtom( _, _ )             =>
        case ETMerge( a, b ) =>
          gatherOccs( a, weak, 1 :: pos )
          gatherOccs( b, weak, 2 :: pos )
        case ETNeg( a ) => gatherOccs( a, weak, 1 :: pos )
        case et: BinaryExpansionTree =>
          gatherOccs( et.child1, weak, 1 :: pos )
          gatherOccs( et.child2, weak, 2 :: pos )
        case ETStrongQuantifier( _, _, ch ) =>
          gatherOccs( ch, weak, 1 :: pos )
        case ETWeakQuantifier( _, insts ) =>
          for ( ( i, ch ) <- insts )
            gatherOccs( ch, i :: weak, 1 :: pos )
        case ETSkolemQuantifier( _, skT, skD, ch ) =>
          gatherOccs( ch, weak, 1 :: pos )
          occs( skT ) += ( ( weak, pos ) )
      }

    for ( ( e, i ) <- es.elements.zip( Stream.from( 1 ) ) ) gatherOccs( e, Nil, i :: Nil )

    // Which Skolem terms occur more than once?
    occs.collect { case ( skT, os ) if os.size > 1 => skT }.toSet
  }
}

object moveSkolemNodesToCuts {

  def apply( ep: ExpansionProof ): ExpansionProof = {
    implicit val nameGen: NameGenerator = rename.awayFrom( ep.eigenVariables ++ freeVariablesET( ep ) )
    val bad = nonProofTheoreticSkolemTerms( ep )
    val cuts = mutable.Buffer[ETImp]()
    def go( et: ExpansionTree ): ExpansionTree =
      et match {
        case _: ETWeakening | _: ETBottom | _: ETTop | _: ETAtom => et
        case ETNeg( f ) => ETNeg( go( f ) )
        case ETAnd( f, g ) => ETAnd( go( f ), go( g ) )
        case ETOr( f, g ) => ETOr( go( f ), go( g ) )
        case ETImp( f, g ) => ETImp( go( f ), go( g ) )
        case ETDefinition( sh, f ) => ETDefinition( sh, go( f ) )
        case ETMerge( f, g ) => ETMerge( go( f ), go( g ) )
        case ETWeakQuantifier( sh, insts ) =>
          ETWeakQuantifier( sh, for ( ( t, f ) <- insts ) yield t -> go( f ) )
        case ETStrongQuantifier( sh, ev, f ) =>
          ETStrongQuantifier( sh, ev, go( f ) )
        case ETSkolemQuantifier( sh, t, d, f ) if !bad( t ) =>
          ETSkolemQuantifier( sh, t, d, go( f ) )
        case ETSkolemQuantifier( sh, t, d, f ) if et.polarity.inSuc =>
          val ( a, b ) = tautAtomicExpansionET( sh )
          cuts += ETImp( ETSkolemQuantifier( sh, t, d, go( f ) ), a )
          b
        case ETSkolemQuantifier( sh, t, d, f ) if et.polarity.inAnt =>
          val ( a, b ) = tautAtomicExpansionET( sh )
          cuts += ETImp( b, ETSkolemQuantifier( sh, t, d, go( f ) ) )
          a
      }
    val es = ep.expansionSequent.map( go )
    ExpansionProof( ETCut( cuts ) +: es )
  }

}
