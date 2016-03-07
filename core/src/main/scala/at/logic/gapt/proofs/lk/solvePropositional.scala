package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import scalaz._
import Scalaz._

trait SolveUtils {
  type Error
  type UnprovableOrLKProof = Error \/ LKProof

  /**
   * Applies the function f, if maybeProof is \/-(proof) and formula is present in polarity pol in proof.
   */
  protected def mapIf( maybeProof: UnprovableOrLKProof, formula: HOLFormula, pol: Boolean )( f: LKProof => LKProof ) =
    maybeProof map { p => if ( p.conclusion.contains( formula, pol ) ) f( p ) else p }

  /**
   * Applies the function f, if maybeProof is \/-(proof) and one of formula{1,2} is present in polarity pol{1,2} in proof.
   */
  protected def mapIf(
    maybeProof: UnprovableOrLKProof,
    formula1:   HOLFormula, pol1: Boolean,
    formula2: HOLFormula, pol2: Boolean
  )( f: LKProof => LKProof ) =
    maybeProof map { p =>
      if ( p.conclusion.contains( formula1, pol1 ) || p.conclusion.contains( formula2, pol2 ) ) f( p )
      else p
    }
}

object solvePropositional extends SolveUtils {
  type Error = HOLSequent

  def apply( formula: HOLFormula ): UnprovableOrLKProof =
    apply( Sequent() :+ formula )

  def apply( seq: HOLSequent ): UnprovableOrLKProof =
    solve( seq ) map { WeakeningMacroRule( _, seq ) }

  private def solve( seq0: HOLSequent ): UnprovableOrLKProof = {
    val seq = seq0.distinct
    None.
      orElse( tryAxiom( seq ) ).
      orElse( tryWeakening( seq ) ).
      orElse( tryNullary( seq ) ).
      orElse( tryUnary( seq ) ).
      orElse( tryBinary( seq ) ).
      getOrElse( seq.left ).
      map {
        ContractionMacroRule( _ ).
          ensuring { _.conclusion isSubsetOf seq }
      }
  }

  private def tryAxiom( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    if ( seq.isTaut )
      Some( LogicalAxiom( seq.antecedent intersect seq.succedent head ).right )
    else
      None

  private def tryNullary( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    seq.zipWithIndex.elements collectFirst {
      case ( Top(), i: Suc )    => TopAxiom.right
      case ( Bottom(), i: Ant ) => BottomAxiom.right
    }

  private def tryWeakening( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    seq.zipWithIndex.elements collectFirst {
      case ( Top(), i: Ant )    => solve( seq delete i )
      case ( Bottom(), i: Suc ) => solve( seq delete i )
    }

  private def tryUnary( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    seq.zipWithIndex.elements collectFirst {
      case ( Neg( f ), i: Ant ) => mapIf( solve( seq.delete( i ) :+ f ), f, true ) { NegLeftRule( _, f ) }
      case ( Neg( f ), i: Suc ) => mapIf( solve( f +: seq.delete( i ) ), f, false ) { NegRightRule( _, f ) }

      case ( e @ And( f, g ), i: Ant ) =>
        mapIf( solve( f +: g +: seq.delete( i ) ), f, false, g, false ) { AndLeftMacroRule( _, f, g ) }
      case ( e @ Or( f, g ), i: Suc ) =>
        mapIf( solve( seq.delete( i ) :+ f :+ g ), f, true, g, true ) { OrRightMacroRule( _, f, g ) }
      case ( e @ Imp( f, g ), i: Suc ) =>
        mapIf( solve( f +: seq.delete( i ) :+ g ), f, false, g, true ) { ImpRightMacroRule( _, f, g ) }
    }

  private def tryBinary( seq: HOLSequent ): Option[UnprovableOrLKProof] = {
    def handle( i: SequentIndex, e: HOLFormula, f: HOLFormula, fPol: Boolean, g: HOLFormula, gPol: Boolean,
                rule: ( LKProof, LKProof, HOLFormula ) => LKProof ) =
      solve( if ( fPol ) seq.delete( i ) :+ f else f +: seq.delete( i ) ) flatMap { p1 =>
        if ( !p1.conclusion.contains( f, fPol ) ) p1.right
        else solve( if ( gPol ) seq.delete( i ) :+ g else g +: seq.delete( i ) ) map { p2 =>
          if ( !p2.conclusion.contains( g, gPol ) ) p2
          else rule( p1, p2, e )
        }
      }

    seq.zipWithIndex.elements collectFirst {
      case ( e @ And( f, g ), i: Suc ) => handle( i, e, f, true, g, true, AndRightRule( _, _, _ ) )
      case ( e @ Or( f, g ), i: Ant )  => handle( i, e, f, false, g, false, OrLeftRule( _, _, _ ) )
      case ( e @ Imp( f, g ), i: Ant ) => handle( i, e, f, true, g, false, ImpLeftRule( _, _, _ ) )
    }
  }

}
