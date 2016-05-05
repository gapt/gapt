package at.logic.gapt.proofs.expansion

import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.provers.escargot.Escargot
import scalaz._
import Scalaz._

object ExpansionProofToLK extends ExpansionProofToLK( Escargot.getLKProof( _, addWeakenings = false ) ) {
  def withTheory( implicit ctx: Context ) = new ExpansionProofToLK( ctx.theory _ )
}
object PropositionalExpansionProofToLK extends ExpansionProofToLK( _ => None )

class ExpansionProofToLK(
    theorySolver: HOLClause => Option[LKProof]
) extends SolveUtils {
  type Error = ( Seq[ETImp], ExpansionSequent )

  def apply( expansionProof: ExpansionProof ): UnprovableOrLKProof =
    apply( ExpansionProofWithCut( expansionProof ) )

  def apply( expansionProofWithCut: ExpansionProofWithCut ): UnprovableOrLKProof =
    solve( expansionProofWithCut.cuts, expansionProofWithCut.expansionSequent ).
      map { WeakeningMacroRule( _, expansionProofWithCut.shallow ) }

  private def solve( cuts: Seq[ETImp], expSeq: ExpansionSequent ): UnprovableOrLKProof =
    None.
      orElse( tryAxiom( cuts, expSeq ) ).
      orElse( tryDef( cuts, expSeq ) ).
      orElse( tryMerge( cuts, expSeq ) ).
      orElse( tryWeakening( cuts, expSeq ) ).
      orElse( tryNullary( cuts, expSeq ) ).
      orElse( tryStrongQ( cuts, expSeq ) ).
      orElse( tryWeakQ( cuts, expSeq ) ).
      orElse( tryUnary( cuts, expSeq ) ).
      orElse( tryCut( cuts, expSeq ) ).
      orElse( tryBinary( cuts, expSeq ) ).
      orElse( tryTheory( cuts, expSeq ) ).
      getOrElse( ( cuts, expSeq ).left ).
      map {
        ContractionMacroRule( _ ).
          ensuring { _.conclusion isSubsetOf expSeq.map { _.shallow } }
      }

  private def tryAxiom( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    val shallowSequent = expSeq map { _.shallow }
    if ( shallowSequent.isTaut )
      Some( LogicalAxiom( shallowSequent.antecedent intersect shallowSequent.succedent head ).right )
    else
      None
  }

  private def tryTheory( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    theorySolver( expSeq collect { case ETAtom( atom, _ ) => atom } ).map { _.right }

  private def tryDef( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( e @ ETDefinedAtom( atom, pol, definition ), i ) =>
        mapIf( solve( cuts, expSeq.updated( i, ETAtom( atom, pol ) ) ), atom, pol ) { DefinitionRule( _, atom, e.shallow, pol ) }
      case ( e @ ETDefinition( sh, defExpr, ch ), i ) =>
        mapIf( solve( cuts, expSeq.updated( i, ch ) ), ch.shallow, i.isSuc ) { DefinitionRule( _, ch.shallow, sh, i.isSuc ) }
    }

  private def tryMerge( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( e @ ETMerge( a, b ), i: Ant ) => solve( cuts, a +: b +: expSeq.delete( i ) )
      case ( e @ ETMerge( a, b ), i: Suc ) => solve( cuts, expSeq.delete( i ) :+ a :+ b )
    }

  private def tryNullary( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETTop( _ ), i: Suc )    => TopAxiom.right
      case ( ETBottom( _ ), i: Ant ) => BottomAxiom.right
    }

  private def tryWeakening( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETWeakening( _, _ ), i ) => solve( cuts, expSeq delete i )
      case ( ETTop( _ ), i: Ant )     => solve( cuts, expSeq delete i )
      case ( ETBottom( _ ), i: Suc )  => solve( cuts, expSeq delete i )
    }

  private def tryUnary( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETNeg( f ), i: Ant ) => mapIf( solve( cuts, expSeq.delete( i ) :+ f ), f.shallow, true ) { NegLeftRule( _, f.shallow ) }
      case ( ETNeg( f ), i: Suc ) => mapIf( solve( cuts, f +: expSeq.delete( i ) ), f.shallow, false ) { NegRightRule( _, f.shallow ) }

      case ( e @ ETAnd( f, g ), i: Ant ) =>
        mapIf( solve( cuts, f +: g +: expSeq.delete( i ) ), f.shallow, false, g.shallow, false ) {
          AndLeftMacroRule( _, f.shallow, g.shallow )
        }
      case ( e @ ETOr( f, g ), i: Suc ) =>
        mapIf( solve( cuts, expSeq.delete( i ) :+ f :+ g ), f.shallow, true, g.shallow, true ) {
          OrRightMacroRule( _, f.shallow, g.shallow )
        }
      case ( e @ ETImp( f, g ), i: Suc ) =>
        mapIf( solve( cuts, f +: expSeq.delete( i ) :+ g ), f.shallow, false, g.shallow, true ) {
          ImpRightMacroRule( _, f.shallow, g.shallow )
        }
    }

  private def tryBinary( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    def handle( i: SequentIndex, e: ExpansionTree, f: ExpansionTree, g: ExpansionTree,
                rule: ( LKProof, LKProof, HOLFormula ) => LKProof ) =
      solve( cuts, if ( f.polarity ) expSeq.delete( i ) :+ f else f +: expSeq.delete( i ) ) flatMap { p1 =>
        if ( !p1.conclusion.contains( f.shallow, f.polarity ) ) p1.right
        else solve( cuts, if ( g.polarity ) expSeq.delete( i ) :+ g else g +: expSeq.delete( i ) ) map { p2 =>
          if ( !p2.conclusion.contains( g.shallow, g.polarity ) ) p2
          else rule( p1, p2, e.shallow )
        }
      }

    expSeq.zipWithIndex.elements collectFirst {
      case ( e @ ETAnd( f, g ), i: Suc ) => handle( i, e, f, g, AndRightRule( _, _, _ ) )
      case ( e @ ETOr( f, g ), i: Ant )  => handle( i, e, f, g, OrLeftRule( _, _, _ ) )
      case ( e @ ETImp( f, g ), i: Ant ) => handle( i, e, f, g, ImpLeftRule( _, _, _ ) )
    }
  }

  private def tryStrongQ( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETStrongQuantifier( sh, ev, f ), i: Ant ) =>
        mapIf( solve( cuts, expSeq.updated( i, f ) ), f.shallow, false ) { ExistsLeftRule( _, sh, ev ) }
      case ( ETStrongQuantifier( sh, ev, f ), i: Suc ) =>
        mapIf( solve( cuts, expSeq.updated( i, f ) ), f.shallow, true ) { ForallRightRule( _, sh, ev ) }
      case ( ETSkolemQuantifier( sh, skT, skD, f ), i: Ant ) =>
        mapIf( solve( cuts, expSeq.updated( i, f ) ), f.shallow, false ) { ExistsSkLeftRule( _, skT, skD ) }
      case ( ETSkolemQuantifier( sh, skT, skD, f ), i: Suc ) =>
        mapIf( solve( cuts, expSeq.updated( i, f ) ), f.shallow, true ) { ForallSkRightRule( _, skT, skD ) }
    }

  private def tryWeakQ( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- cuts ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet
    def possibleInsts( insts: Map[LambdaExpression, ExpansionTree] ) =
      insts filterKeys { t => freeVariables( t ) intersect upcomingEVs isEmpty }

    expSeq.zipWithIndex.elements collectFirst {
      case ( ETWeakQuantifier( sh, insts ), i ) if possibleInsts( insts ).nonEmpty =>
        val insts_ = possibleInsts( insts )

        var newExpSeq =
          if ( insts_ == insts ) expSeq.delete( i )
          else expSeq.updated( i, ETWeakQuantifier( sh, insts -- insts_.keys ) )

        if ( i isSuc ) newExpSeq :++= insts_.values
        else newExpSeq ++:= insts_.values

        solve( cuts, newExpSeq ) map { p0 =>
          insts_.foldLeft( p0 ) {
            case ( p, ( _, child ) ) if !p.conclusion.contains( child.shallow, i.isSuc ) => p
            case ( p, ( t, _ ) ) if i isAnt => ForallLeftRule( p, sh, t )
            case ( p, ( t, _ ) ) if i isSuc => ExistsRightRule( p, sh, t )
          }
        }
    }
  }

  private def tryCut( cuts: Seq[ETImp], expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- cuts ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet

    cuts.zipWithIndex collectFirst {
      case ( ETImp( cut1, cut2 ), i ) if freeVariables( cut1.shallow ) intersect upcomingEVs isEmpty =>
        val newCuts = cuts.zipWithIndex.filter { _._2 != i }.map { _._1 }
        solve( newCuts, expSeq :+ cut1 ) flatMap { p1 =>
          if ( !p1.conclusion.contains( cut1.shallow, true ) ) p1.right
          else solve( newCuts, cut2 +: expSeq ) map { p2 =>
            if ( !p2.conclusion.contains( cut2.shallow, false ) ) p2
            else CutRule( p1, p2, cut1.shallow )
          }
        }
    }
  }

}
