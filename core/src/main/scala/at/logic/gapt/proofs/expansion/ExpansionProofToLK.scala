package at.logic.gapt.proofs.expansion

import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs.Context.StructurallyInductiveTypes
import at.logic.gapt.provers.escargot.Escargot

object ExpansionProofToLK extends ExpansionProofToLK( Escargot.getAtomicLKProof ) {
  def withTheory( implicit ctx: Context ) = new ExpansionProofToLK( FOTheoryMacroRule.option( _ ) )
}
object PropositionalExpansionProofToLK extends ExpansionProofToLK( _ => None )

class ExpansionProofToLK(
    theorySolver: HOLClause => Option[LKProof] ) extends SolveUtils {
  type Error = ( Seq[ETImp], ExpansionSequent )

  abstract class Case
  case class StepCase( evs: Seq[Var], atoms: List[ETAtom] ) extends Case
  case class BaseCase( atom: ETAtom ) extends Case

  case class Induction( constructorsSteps: Seq[( Const, Case )], hyps: ExpansionTree, suc: ETWeakQuantifier )
  case class Theory( cuts: Seq[ETImp], inductions: Seq[Induction] ) {
    def getExpansionTrees: Seq[ETImp] = cuts ++ inductions.map( i => ETImp( i.hyps, i.suc ) )
  }

  def apply( expansionProof: ExpansionProof )( implicit ctx: Context = Context() ): UnprovableOrLKProof = {

    val indAxioms = ctx.get[StructurallyInductiveTypes].constructors.map {
      case ( s, cs ) => ( makeInductionExplicit.inductionPrinciple( TBase( s ), cs ), cs )
    }

    def getAtoms( et: ExpansionTree ): List[ETAtom] = {
      et match {
        case ETStrongQuantifier( _, _, ch ) => getAtoms( ch )
        case ETImp( ch1, ch2 )              => getAtoms( ch1 ) ++ getAtoms( ch2 )
        case a: ETAtom                      => List( a )
      }
    }
    def getEvs( et: ExpansionTree ): List[Var] = {
      et match {
        case ETStrongQuantifier( _, ev, ch ) => ev :: getEvs( ch )
        case _                               => List.empty
      }
    }
    def toCase( et: ExpansionTree ): Case = {
      et match {
        case q @ ETStrongQuantifier( _, _, ch ) => StepCase( getEvs( q ), getAtoms( ch ) )
        case a: ETAtom                          => BaseCase( a )
      }
    }

    val inductions = for {
      inductionAxiomExpansion <- expansionProof.expansionSequent.antecedent
      if indAxioms.contains( inductionAxiomExpansion.shallow )
      sequent <- inductionAxiomExpansion( HOLPosition( 1 ) )
      hyps <- sequent( HOLPosition( 1 ) )
      suc <- sequent( HOLPosition( 2 ) )
      cs = indAxioms( inductionAxiomExpansion.shallow )
    } yield Induction( cs.zip( hyps.immediateSubProofs.map( toCase( _ ) ) ), hyps, suc.asInstanceOf[ETWeakQuantifier] )

    solve( Theory( expansionProof.cuts, inductions ), expansionProof.nonCutPart filter { x => !indAxioms.contains( x.shallow ) } ).
      map( WeakeningMacroRule( _, expansionProof.nonCutPart.shallow filter { x => !indAxioms.contains( x ) } ) )

  }

  private def solve( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): UnprovableOrLKProof = {
    None.
      orElse( tryAxiom( theory, expSeq ) ).
      orElse( tryDef( theory, expSeq ) ).
      orElse( tryMerge( theory, expSeq ) ).
      orElse( tryWeakening( theory, expSeq ) ).
      orElse( tryNullary( theory, expSeq ) ).
      orElse( tryStrongQ( theory, expSeq ) ).
      orElse( tryWeakQ( theory, expSeq ) ).
      orElse( tryUnary( theory, expSeq ) ).
      orElse( tryCut( theory, expSeq ) ).
      orElse( tryInduction( theory, expSeq ) ).
      orElse( tryBinary( theory, expSeq ) ).
      orElse( tryTheory( theory, expSeq ) ).
      getOrElse( Left( ( theory.getExpansionTrees ) -> expSeq ) ).
      map {
        ContractionMacroRule( _ ).
          ensuring { _.conclusion isSubsetOf expSeq.shallow }
      }
  }

  private def tryAxiom( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    val shallowSequent = expSeq.shallow
    if ( shallowSequent.isTaut )
      Some( Right( LogicalAxiom( shallowSequent.antecedent intersect shallowSequent.succedent head ) ) )
    else
      None
  }

  private def tryTheory( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    theorySolver( expSeq collect { case ETAtom( atom, _ ) => atom } ).map {
      Right( _ )
    }

  private def tryDef( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETDefinition( sh, ch ), i ) =>
        mapIf( solve( theory, expSeq.updated( i, ch ) ), ch.shallow, i.polarity ) {
          DefinitionRule( _, ch.shallow, sh, i.polarity )
        }
    }

  private def tryMerge( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( e @ ETMerge( a, b ), i: Ant ) => solve( theory, a +: b +: expSeq.delete( i ) )
      case ( e @ ETMerge( a, b ), i: Suc ) => solve( theory, expSeq.delete( i ) :+ a :+ b )
    }

  private def tryNullary( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETTop( _ ), i: Suc )    => Right( TopAxiom )
      case ( ETBottom( _ ), i: Ant ) => Right( BottomAxiom )
    }

  private def tryWeakening( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETWeakening( _, _ ), i ) => solve( theory, expSeq delete i )
      case ( ETTop( _ ), i: Ant )     => solve( theory, expSeq delete i )
      case ( ETBottom( _ ), i: Suc )  => solve( theory, expSeq delete i )
    }

  private def tryUnary( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETNeg( f ), i: Ant ) => mapIf( solve( theory, expSeq.delete( i ) :+ f ), f.shallow, !i.polarity ) {
        NegLeftRule( _, f.shallow )
      }
      case ( ETNeg( f ), i: Suc ) => mapIf( solve( theory, f +: expSeq.delete( i ) ), f.shallow, !i.polarity ) {
        NegRightRule( _, f.shallow )
      }
      case ( e @ ETAnd( f, g ), i: Ant ) =>
        mapIf( solve( theory, f +: g +: expSeq.delete( i ) ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          AndLeftMacroRule( _, f.shallow, g.shallow )
        }
      case ( e @ ETOr( f, g ), i: Suc ) =>
        mapIf( solve( theory, expSeq.delete( i ) :+ f :+ g ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          OrRightMacroRule( _, f.shallow, g.shallow )
        }
      case ( e @ ETImp( f, g ), i: Suc ) =>
        mapIf( solve( theory, f +: expSeq.delete( i ) :+ g ), f.shallow, !i.polarity, g.shallow, i.polarity ) {
          ImpRightMacroRule( _, f.shallow, g.shallow )
        }
    }

  private def tryBinary( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    def handle( i: SequentIndex, e: ExpansionTree, f: ExpansionTree, g: ExpansionTree,
                rule: ( LKProof, LKProof, Formula ) => LKProof ) =
      solve( theory, if ( f.polarity.inSuc ) expSeq.delete( i ) :+ f else f +: expSeq.delete( i ) ) flatMap { p1 =>
        if ( !p1.conclusion.contains( f.shallow, f.polarity ) ) Right( p1 )
        else solve( theory, if ( g.polarity.inSuc ) expSeq.delete( i ) :+ g else g +: expSeq.delete( i ) ) map { p2 =>
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

  private def tryStrongQ( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETStrongQuantifier( sh, ev, f ), i: Ant ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ExistsLeftRule( _, sh, ev )
        }
      case ( ETStrongQuantifier( sh, ev, f ), i: Suc ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ForallRightRule( _, sh, ev )
        }
      case ( ETSkolemQuantifier( sh, skT, skD, f ), i: Ant ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ExistsSkLeftRule( _, skT, skD )
        }
      case ( ETSkolemQuantifier( sh, skT, skD, f ), i: Suc ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ForallSkRightRule( _, skT, skD )
        }
    }

  private def tryWeakQ( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- theory.getExpansionTrees ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet
    def possibleInsts( insts: Map[Expr, ExpansionTree] ) =
      Map() ++ insts.filterKeys( t => freeVariables( t ) intersect upcomingEVs isEmpty )

    for ( ( ETWeakQuantifier( sh, insts ), i ) <- expSeq.zipWithIndex.elements ) {
      val insts_ = possibleInsts( insts )

      if ( insts_.nonEmpty ) {
        var newExpSeq =
          if ( insts_ == insts ) expSeq.delete( i )
          else expSeq.updated( i, ETWeakQuantifier( sh, insts -- insts_.keys ) )

        if ( i isSuc ) newExpSeq :++= insts_.values
        else newExpSeq ++:= insts_.values

        return Some( solve( theory, newExpSeq ) map { p0 =>
          insts_.foldLeft( p0 ) {
            case ( p, ( _, child ) ) if !p.conclusion.contains( child.shallow, i.polarity ) => p
            case ( p, ( t, _ ) ) if i isAnt => ForallLeftRule( p, sh, t )
            case ( p, ( t, _ ) ) if i isSuc => ExistsRightRule( p, sh, t )
          }
        } )
      }
    }
    None
  }

  private def tryCut( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- theory.getExpansionTrees ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet

    theory.cuts.zipWithIndex collectFirst {
      case ( ETImp( cut1, cut2 ), i ) if freeVariables( cut1.shallow ) intersect upcomingEVs isEmpty =>
        val newCuts = theory.cuts.zipWithIndex.filter { _._2 != i }.map { _._1 }
        solve( Theory( newCuts, theory.inductions ), expSeq :+ cut1 ) flatMap { p1 =>
          if ( !p1.conclusion.contains( cut1.shallow, Polarity.InSuccedent ) ) Right( p1 )
          else solve( Theory( newCuts, theory.inductions ), cut2 +: expSeq ) map { p2 =>
            if ( !p2.conclusion.contains( cut2.shallow, Polarity.InAntecedent ) ) p2
            else CutRule( p1, p2, cut1.shallow )
          }
        }
    }
  }

  private def tryInduction( theory: Theory, expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    val upcomingEVs = ( for {
      et <- theory.getExpansionTrees ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet

    theory.inductions.zipWithIndex.collectFirst {
      case ( Induction( constructorsSteps, hyps, suc ), i ) if freeVariables( hyps.shallow ) intersect upcomingEVs isEmpty =>

        val newInductions = theory.inductions.zipWithIndex.filter { _._2 != i }.map { _._1 }

        def recSteps( constructorsSteps: Seq[( Const, Case )], cases: Seq[InductionCase] ): UnprovableOrLKProof = {
          constructorsSteps match {
            case ( c, BaseCase( atom ) ) +: tail =>
              solve( Theory( theory.cuts, newInductions ), expSeq :+ atom ) flatMap { p =>
                if ( !p.conclusion.contains( atom.shallow, Polarity.InSuccedent ) ) Right( p )
                else {
                  val sIdx = p.conclusion.indexOf( atom.shallow, Polarity.InSuccedent )
                  recSteps( tail, InductionCase( p, c, Seq.empty, Seq.empty, sIdx ) +: cases )
                }
              }
            case ( c, StepCase( evs, atoms ) ) +: tail =>
              val ( ant, suc ) = atoms.splitAt( atoms.length - 1 )
              solve( Theory( theory.cuts, newInductions ), ant ++: expSeq :++ suc ) flatMap { p =>
                if ( !( ant.forall( a => p.conclusion.contains( a.shallow, Polarity.InAntecedent ) )
                  && p.conclusion.contains( suc.head.shallow, Polarity.InSuccedent ) ) ) Right( p )
                else {
                  val aIdxs = ant.map( a => p.conclusion.indexOf( a.shallow, Polarity.InAntecedent ) )
                  val sIdx = p.conclusion.indexOf( suc.head.shallow, Polarity.InSuccedent )
                  recSteps( tail, InductionCase( p, c, aIdxs, evs, sIdx ) +: cases )
                }
              }
            case tail if tail.isEmpty =>
              val App( _, qfFormula: Abs ) = suc.shallow
              val ( v: Expr, _ ) = suc.instances.head

              val ir = InductionRule( cases, qfFormula, v )
              val phit = ETAtom( Atom( ir.conclusion.succedent.head ), Polarity.InAntecedent )
              solve( Theory( theory.cuts, newInductions ), phit +: expSeq ) map { p =>
                if ( !p.conclusion.contains( phit.shallow, Polarity.InAntecedent ) ) p
                else {
                  // TODO simplify to ir if p3 is just an axiom?
                  CutRule( ir, p, phit.shallow )
                }
              }
          }
        }
        recSteps( constructorsSteps, Seq.empty )
    }
  }

}
