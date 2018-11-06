package gapt.proofs.expansion
import gapt.expr._
import gapt.utils.NameGenerator

import scala.collection.mutable

object tautAtomicExpansionET {
  import Polarity._
  def apply( formula: Formula )( implicit nameGen: NameGenerator ): ( ExpansionTree, ExpansionTree ) = {
    val ( f1, f2 ) = asTerm( formula )
    ExpansionTree( formula, InAntecedent, f1 ) -> ExpansionTree( formula, InSuccedent, f2 )
  }
  def asTerm( formula: Formula )( implicit nameGen: NameGenerator ): ( ETt, ETt ) = formula match {
    case Top() | Bottom() => ETtNullary -> ETtNullary
    case _: Atom          => ETtAtom -> ETtAtom
    case Neg( f ) =>
      val ( f1, f2 ) = asTerm( f )
      ETtUnary( f2 ) -> ETtUnary( f1 )
    case And( f, g ) =>
      val ( f1, f2 ) = asTerm( f )
      val ( g1, g2 ) = asTerm( g )
      ETtBinary( f1, g1 ) -> ETtBinary( f2, g2 )
    case Or( f, g ) =>
      val ( f1, f2 ) = asTerm( f )
      val ( g1, g2 ) = asTerm( g )
      ETtBinary( f1, g1 ) -> ETtBinary( f2, g2 )
    case Imp( f, g ) =>
      val ( f1, f2 ) = asTerm( f )
      val ( g1, g2 ) = asTerm( g )
      ETtBinary( f2, g1 ) -> ETtBinary( f1, g2 )
    case All( x0, f ) =>
      val x = nameGen.fresh( x0 )
      val ( f1, f2 ) = asTerm( f )
      ETtWeak( x -> f1 ) -> ETtStrong( x, f2 )
    case Ex( x0, f ) =>
      val x = nameGen.fresh( x0 )
      val ( f1, f2 ) = asTerm( f )
      ETtStrong( x, f1 ) -> ETtWeak( x -> f2 )
  }
}

object nonProofTheoreticSkolemTerms {
  def apply( ep: ExpansionProof ): Set[Expr] = apply( ep.expansionSequent )
  def apply( es: ExpansionSequent ): Set[Expr] = {
    val occs = mutable.Map[Expr, Set[( List[Expr], List[Int] )]]().withDefaultValue( Set.empty )
    def gatherOccs( et: ETt, weak: List[Expr], pos: List[Int] ): Unit =
      et match {
        case ETtNullary | ETtWeakening | ETtAtom =>
        case ETtMerge( a, b ) =>
          gatherOccs( a, weak, 1 :: pos )
          gatherOccs( b, weak, 2 :: pos )
        case ETtUnary( a ) => gatherOccs( a, weak, 1 :: pos )
        case ETtBinary( child1, child2 ) =>
          gatherOccs( child1, weak, 1 :: pos )
          gatherOccs( child2, weak, 2 :: pos )
        case ETtDef( _, ch ) =>
          gatherOccs( ch, weak, 1 :: pos )
        case ETtStrong( _, ch ) =>
          gatherOccs( ch, weak, 1 :: pos )
        case ETtWeak( insts ) =>
          for ( ( i, ch ) <- insts )
            gatherOccs( ch, i :: weak, 1 :: pos )
        case ETtSkolem( skT, _, ch ) =>
          gatherOccs( ch, weak, 1 :: pos )
          occs( skT ) += ( ( weak, pos ) )
      }

    for ( ( e, i ) <- es.elements.zip( Stream.from( 1 ) ) ) gatherOccs( e.term, Nil, i :: Nil )

    // Which Skolem terms occur more than once?
    occs.collect { case ( skT, os ) if os.size > 1 => skT }.toSet
  }
}

object moveSkolemNodesToCuts {

  def apply( ep: ExpansionProof ): ExpansionProof = {
    val bad = nonProofTheoreticSkolemTerms( ep )
    if ( bad.isEmpty ) return ep
    implicit val nameGen: NameGenerator = rename.awayFrom( ep.eigenVariables ++ freeVariablesET( ep ) )
    val cuts = mutable.Buffer[ETCut.Cut]()
    def go( et: ExpansionTree ): ExpansionTree =
      et match {
        case ETWeakening( _, _ ) | ETBottom( _ ) | ETTop( _ ) | ETAtom( _, _ ) => et
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
          cuts += ( ETSkolemQuantifier( sh, t, d, go( f ) ) -> a )
          b
        case ETSkolemQuantifier( sh, t, d, f ) if et.polarity.inAnt =>
          val ( a, b ) = tautAtomicExpansionET( sh )
          cuts += ( b -> ETSkolemQuantifier( sh, t, d, go( f ) ) )
          a
      }
    val es = ep.expansionSequent.map( go )
    ExpansionProof( ETCut( cuts ) +: es )
  }

}
