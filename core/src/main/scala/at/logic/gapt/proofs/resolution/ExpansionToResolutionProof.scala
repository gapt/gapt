package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, Sequent, Suc }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.escargot.Escargot

/** Converts an expansion proof to a resolution proof. */
object ExpansionToResolutionProof {

  def apply( expansionProof: ExpansionProof, prover: ResolutionProver = Escargot ): Option[ResolutionProof] =
    prover.getResolutionProof( asCNF( expansionProof ) )

  /** Just the CNF of the deep formula of the expansion proof. */
  def asCNF( expansionProof: ExpansionProof ): Set[ResolutionProof] =
    expansionProof.expansionSequent.
      map( Sequent() :+ _, _ +: Sequent() ).elements.view.
      flatMap( es => clausify( es, Input( es.shallow ) ) ).toSet

  private def clausify( expansionSequent: ExpansionSequent, proof: ResolutionProof ): Set[ResolutionProof] =
    None.
      orElse( tryUnaryOrNullary( expansionSequent, proof ) ).
      orElse( tryNAry( expansionSequent, proof ) ).
      getOrElse( Set( proof ) )

  private def tryUnaryOrNullary( es: ExpansionSequent, p: ResolutionProof ): Option[Set[ResolutionProof]] =
    es.zipWithIndex.elements.collectFirst {
      case ( ETWeakening( _, _ ), _ ) => Set()

      case ( ETTop( _ ), i: Suc )     => Set()
      case ( ETBottom( _ ), i: Ant )  => Set()
      case ( ETTop( _ ), i: Ant )     => clausify( es.delete( i ), TopL( p, i ) )
      case ( ETBottom( _ ), i: Suc )  => clausify( es.delete( i ), BottomR( p, i ) )

      case ( ETNeg( child ), i: Ant ) => clausify( es.delete( i ) :+ child, NegL( p, i ) )
      case ( ETNeg( child ), i: Suc ) => clausify( child +: es.delete( i ), NegR( p, i ) )

      case ( ETAnd( a, b ), i: Ant )  => clausify( a +: b +: es.delete( i ), AndL( p, i ) )
      case ( ETOr( a, b ), i: Suc )   => clausify( es.delete( i ) :+ a :+ b, OrR( p, i ) )
      case ( ETImp( a, b ), i: Suc )  => clausify( a +: es.delete( i ) :+ b, ImpR( p, i ) )

      case ( ETSkolemQuantifier( sh, skTerm, skDef, child ), i: Ant ) =>
        clausify( child +: es.delete( i ), AllL( p, i, skTerm, skDef ) )
      case ( ETSkolemQuantifier( sh, skTerm, skDef, child ), i: Suc ) =>
        clausify( es.delete( i ) :+ child, ExR( p, i, skTerm, skDef ) )
    }

  private def tryNAry( es: ExpansionSequent, p: ResolutionProof ): Option[Set[ResolutionProof]] =
    es.zipWithIndex.elements.collectFirst {
      case ( ETAnd( a, b ), i: Suc ) =>
        clausify( es.delete( i ) :+ a, AndR1( p, i ) ) union
          clausify( es.delete( i ) :+ b, AndR2( p, i ) )
      case ( ETOr( a, b ), i: Ant ) =>
        clausify( a +: es.delete( i ), OrL1( p, i ) ) union
          clausify( b +: es.delete( i ), OrL2( p, i ) )
      case ( ETImp( a, b ), i: Ant ) =>
        clausify( es.delete( i ) :+ a, ImpL1( p, i ) ) union
          clausify( b +: es.delete( i ), ImpL2( p, i ) )

      case ( ETWeakQuantifier( sh @ Quant( v, _, isForall ), insts ), i ) =>
        val ev = rename( v, freeVariables( p.conclusion ) )
        val p1 = if ( i.isAnt ) ExL( p, i, ev ) else AllR( p, i, ev )
        insts.flatMap {
          case ( term, child ) =>
            clausify(
              if ( i.isAnt ) child +: es.delete( i )
              else es.delete( i ) :+ child,
              Subst( p1, Substitution( ev -> term ) )
            )
        }.toSet
    }

}
