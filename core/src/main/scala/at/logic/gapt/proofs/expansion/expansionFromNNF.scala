package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ instantiate, toNNF }
import at.logic.gapt.proofs.{ HOLSequent, Sequent }

object expansionFromNNF {

  private implicit class RichPair[A, B]( val pair: ( A, B ) ) extends AnyVal {
    def map1[A_]( f: A => A_ ): ( A_, B ) = ( f( pair._1 ), pair._2 )
    def map2[B_]( f: B => B_ ): ( A, B_ ) = ( pair._1, f( pair._2 ) )
  }
  private implicit class RichListPair[A, B]( val pair: ( A, List[B] ) ) extends AnyVal {
    def get1: A = {
      require( pair._2.isEmpty )
      pair._1
    }
  }

  private def numClauses( f: HOLFormula, pol: Boolean, vs: Set[Var] ): Int = f match {
    case Top() | Bottom() => 0
    case Neg( g ) => numClauses( g, !pol, vs )
    case And( a, b ) if !pol => numClauses( a, pol, vs ) + numClauses( b, pol, vs )
    case Or( a, b ) if pol => numClauses( a, pol, vs ) + numClauses( b, pol, vs )
    case Imp( a, b ) if pol => numClauses( a, !pol, vs ) + numClauses( b, pol, vs )
    case Ex( v, g ) => numClauses( g, pol, vs + v )
    case All( v, g ) => numClauses( g, pol, vs + v )
    case _ if freeVariables( f ).intersect( vs ).nonEmpty => 1
    case _ => 0
  }

  def apply( nnf: List[ExpansionTree], sh: HOLFormula, pol: Boolean, mode: Boolean ): ( ExpansionTree, List[ExpansionTree] ) =
    ( nnf, sh, mode == pol ) match {
      case ( ETOr( a, b ) :: nnf_, _, _ ) if mode   => apply( a :: b :: nnf_, sh, pol, mode )
      case ( ETAnd( a, b ) :: nnf_, _, _ ) if !mode => apply( a :: b :: nnf_, sh, pol, mode )

      case ( ( ETOr( ETTop( _ ), _ ) | ETOr( _, ETTop( _ ) ) | ETAnd( ETBottom( _ ), _ ) | ETAnd( _, ETBottom( _ ) ) ) :: nnf_, _, _ ) =>
        apply( nnf_, sh, pol, mode )
      case ( ETOr( ETBottom( _ ), a ) :: nnf_, _, _ ) => apply( a :: nnf_, sh, pol, mode )
      case ( ETOr( a, ETBottom( _ ) ) :: nnf_, _, _ ) => apply( a :: nnf_, sh, pol, mode )
      case ( ETAnd( ETTop( _ ), a ) :: nnf_, _, _ )   => apply( a :: nnf_, sh, pol, mode )
      case ( ETAnd( a, ETTop( _ ) ) :: nnf_, _, _ )   => apply( a :: nnf_, sh, pol, mode )

      case ( ETWeakening( And( a, b ), p ) :: nnf_, _, false ) =>
        apply( ETAnd( ETWeakening( a, p ), ETWeakening( b, p ) ) :: nnf_, sh, pol, mode )
      case ( ETWeakening( Or( a, b ), p ) :: nnf_, _, true ) =>
        apply( ETOr( ETWeakening( a, p ), ETWeakening( b, p ) ) :: nnf_, sh, pol, mode )
      case ( ETWeakening( Or( a, b ), p ) :: nnf_, _, true ) =>
        apply( ETImp( ETWeakening( a, !p ), ETWeakening( b, p ) ) :: nnf_, sh, pol, mode )
      case ( ETWeakening( Neg( _: HOLAtom ) | ( _: HOLAtom ), _ ) :: nnf_, _, _ ) => apply( nnf_, sh, pol, mode )

      case ( ( ETTop( _ ) | ETBottom( _ ) | ETAtom( _, _ ) | ETNeg( ETAtom( _, _ ) ) ) :: nnf_, _, _ ) =>
        apply( nnf_, sh, pol, mode )
      case ( nnf_, atom: HOLAtom, _ ) => ( ETAtom( atom, pol ), nnf_ )
      case ( _, Neg( f ), _ )         => apply( nnf, f, !pol, mode ).map1( ETNeg( _ ) )
      case ( _, Top(), _ )            => ( ETTop( pol ), nnf )
      case ( _, Bottom(), _ )         => ( ETBottom( pol ), nnf )
      case ( _, And( f, g ), false ) =>
        val ( f_, nnf_ ) = apply( nnf, f, pol, mode )
        apply( nnf_, g, pol, mode ).map1( ETAnd( f_, _ ) )
      case ( _, Or( f, g ), true ) =>
        val ( f_, nnf_ ) = apply( nnf, f, pol, mode )
        apply( nnf_, g, pol, mode ).map1( ETOr( f_, _ ) )
      case ( _, Imp( f, g ), true ) =>
        val ( f_, nnf_ ) = apply( nnf, f, !pol, mode )
        apply( nnf_, g, pol, mode ).map1( ETImp( f_, _ ) )

      case ( ETWeakening( _, _ ) :: nnf_, _, _ ) =>
        ( ETWeakening( sh, pol ), nnf_ )

      case ( _, Quant( v, f ), _ ) =>
        val nc = numClauses( sh, pol, Set() )
        val insts = for {
          i <- 0 until nc
          ETWeakQuantifier( _, is ) = nnf( i )
          ( t, inst ) <- is
        } yield t -> ETOr( for ( j <- 0 until nc ) yield if ( i == j ) inst else ETWeakening( instantiate( nnf( j ).shallow, t ), true ), true )
        ( ETWeakQuantifier.withMerge( sh, for ( ( term, inst ) <- insts )
          yield term -> apply( List( inst ), instantiate( sh, term ), pol, true ).get1 ), nnf.drop( nc ) )
      case ( a :: nnf_, And( _, _ ), true )               => ( apply( List( a ), sh, pol, !mode ).get1, nnf_ )
      case ( a :: nnf_, Or( _, _ ) | Imp( _, _ ), false ) => ( apply( List( a ), sh, pol, !mode ).get1, nnf_ )
    }

  def apply( nnf: List[ExpansionTree], sh: HOLSequent ): ExpansionSequent =
    if ( sh isEmpty ) {
      Sequent()
    } else {
      val ( shf, i ) =
        if ( sh.antecedent.nonEmpty ) sh.zipWithIndex.elements.head
        else sh.zipWithIndex.elements.last
      val ( et, nnf_ ) = apply( nnf, shf, i.isSuc, true )
      val rest = apply( nnf_, sh delete i )
      if ( i.isAnt ) et +: rest else rest :+ et
    }
}
