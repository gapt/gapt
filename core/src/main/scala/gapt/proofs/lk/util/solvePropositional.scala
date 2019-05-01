package gapt.proofs.lk.util

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.logic.Polarity
import gapt.proofs._
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.macros.AndLeftMacroRule
import gapt.proofs.lk.rules.macros.ContractionMacroRule
import gapt.proofs.lk.rules.macros.ImpRightMacroRule
import gapt.proofs.lk.rules.macros.OrRightMacroRule
import gapt.proofs.lk.rules.macros.WeakeningMacroRule
import gapt.provers.escargot.Escargot

trait SolveUtils {
  type Error
  type UnprovableOrLKProof = Either[Error, LKProof]

  /**
   * Applies the function f, if maybeProof is Right(proof) and formula is present in polarity pol in proof.
   */
  protected final def mapIf( maybeProof: UnprovableOrLKProof, formula: Formula, pol: Polarity )( f: LKProof => LKProof ) =
    maybeProof map { p => if ( p.conclusion.contains( formula, pol ) ) f( p ) else p }

  /**
   * Applies the function f, if maybeProof is Right(proof) and one of formula{1,2} is present in polarity pol{1,2} in proof.
   */
  protected final def mapIf(
    maybeProof: UnprovableOrLKProof,
    formula1:   Formula, pol1: Polarity,
    formula2: Formula, pol2: Polarity )( f: LKProof => LKProof ) =
    maybeProof map { p =>
      if ( p.conclusion.contains( formula1, pol1 ) || p.conclusion.contains( formula2, pol2 ) ) f( p )
      else p
    }
}

object solvePropositional extends solvePropositional( _ => None )
object solveQuasiPropositional extends solvePropositional( Escargot.getAtomicLKProof )

class solvePropositional(
    theorySolver: HOLClause => Option[LKProof] ) extends SolveUtils {
  type Error = HOLSequent

  def apply( formula: Formula ): UnprovableOrLKProof =
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
      orElse( tryTheory( seq ) ).
      getOrElse( Left( seq ) ).
      map {
        ContractionMacroRule( _ ).
          ensuring { _.conclusion isSubsetOf seq }
      }
  }

  private def tryAxiom( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    if ( seq.isTaut )
      Some( Right( LogicalAxiom( seq.antecedent intersect seq.succedent head ) ) )
    else
      None

  private def tryNullary( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    seq.zipWithIndex.elements collectFirst {
      case ( Top(), i: Suc )    => Right( TopAxiom )
      case ( Bottom(), i: Ant ) => Right( BottomAxiom )
    }

  private def tryWeakening( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    seq.zipWithIndex.elements collectFirst {
      case ( Top(), i: Ant )    => solve( seq delete i )
      case ( Bottom(), i: Suc ) => solve( seq delete i )
    }

  private def tryUnary( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    seq.zipWithIndex.elements collectFirst {
      case ( Neg( f ), i: Ant ) => mapIf( solve( seq.delete( i ) :+ f ), f, !i.polarity ) { NegLeftRule( _, f ) }
      case ( Neg( f ), i: Suc ) => mapIf( solve( f +: seq.delete( i ) ), f, !i.polarity ) { NegRightRule( _, f ) }

      case ( e @ And( f, g ), i: Ant ) =>
        mapIf( solve( f +: g +: seq.delete( i ) ), f, i.polarity, g, i.polarity ) { AndLeftMacroRule( _, f, g ) }
      case ( e @ Or( f, g ), i: Suc ) =>
        mapIf( solve( seq.delete( i ) :+ f :+ g ), f, i.polarity, g, i.polarity ) { OrRightMacroRule( _, f, g ) }
      case ( e @ Imp( f, g ), i: Suc ) =>
        mapIf( solve( f +: seq.delete( i ) :+ g ), f, !i.polarity, g, i.polarity ) { ImpRightMacroRule( _, f, g ) }
    }

  private def tryBinary( seq: HOLSequent ): Option[UnprovableOrLKProof] = {
    def handle( i: SequentIndex, e: Formula, f: Formula, fPol: Polarity, g: Formula, gPol: Polarity,
                rule: ( LKProof, LKProof, Formula ) => LKProof ) =
      solve( if ( fPol.inSuc ) seq.delete( i ) :+ f else f +: seq.delete( i ) ) flatMap { p1 =>
        if ( !p1.conclusion.contains( f, fPol ) ) Right( p1 )
        else solve( if ( gPol.inSuc ) seq.delete( i ) :+ g else g +: seq.delete( i ) ) map { p2 =>
          if ( !p2.conclusion.contains( g, gPol ) ) p2
          else rule( p1, p2, e )
        }
      }

    seq.zipWithIndex.elements collectFirst {
      case ( e @ And( f, g ), i: Suc ) => handle( i, e, f, i.polarity, g, i.polarity, AndRightRule( _, _, _ ) )
      case ( e @ Or( f, g ), i: Ant )  => handle( i, e, f, i.polarity, g, i.polarity, OrLeftRule( _, _, _ ) )
      case ( e @ Imp( f, g ), i: Ant ) => handle( i, e, f, !i.polarity, g, i.polarity, ImpLeftRule( _, _, _ ) )
    }
  }

  private def tryTheory( seq: HOLSequent ): Option[UnprovableOrLKProof] =
    theorySolver( seq collect { case atom: Atom => atom } ).map( Right( _ ) )

}
