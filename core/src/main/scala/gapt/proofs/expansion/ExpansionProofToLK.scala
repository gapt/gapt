package gapt.proofs.expansion

import gapt.expr._
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.proofs.lk._
import gapt.proofs.lk.rules.AndLeftMacroRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionMacroRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.DefinitionRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.FOTheoryMacroRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightMacroRule
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightMacroRule
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningMacroRule
import gapt.proofs.lk.util.SolveUtils
import gapt.provers.escargot.Escargot
import gapt.utils.quiet

object ExpansionProofToLK extends ExpansionProofToLK( Escargot.getAtomicLKProof, intuitionisticHeuristics = false ) {
  object withIntuitionisticHeuristics extends ExpansionProofToLK(
    Escargot.getAtomicLKProof, intuitionisticHeuristics = true )
  def withTheory( implicit ctx: Context ) = new ExpansionProofToLK( FOTheoryMacroRule.option( _ ) )

  override def apply( expansionProof: ExpansionProof )( implicit ctx: Context = Context.guess( expansionProof.deep.elements ) ): UnprovableOrLKProof =
    new ExpansionProofToLK( Escargot.getAtomicLKProof( _ )( ctx ), intuitionisticHeuristics = false ).
      apply( expansionProof ).asInstanceOf[UnprovableOrLKProof]
}
object PropositionalExpansionProofToLK extends ExpansionProofToLK( _ => None )

class ExpansionProofToLK(
    theorySolver:             HOLClause => Option[LKProof],
    intuitionisticHeuristics: Boolean                      = false ) extends SolveUtils {
  case class Theory( cuts: Seq[ETCut.Cut], inductions: Seq[ETInduction.Induction] ) {
    def getExpansionTrees: Seq[ExpansionTree] =
      ( cuts ++ inductions.map( i => ETCut.Cut( i.hyps, i.suc ) ) ).map( _.toImp )
  }
  type Error = ( Theory, ExpansionSequent )

  def apply( expansionProof: ExpansionProof )( implicit ctx: Context = Context() ): UnprovableOrLKProof = {
    solve( Theory( expansionProof.cuts, expansionProof.inductions ), expansionProof.nonTheoryPart ).
      map( WeakeningMacroRule( _, expansionProof.nonTheoryPart.shallow ) )
  }

  private def solve( theory: Theory, expSeq: ExpansionSequent ): UnprovableOrLKProof = {
    None.
      orElse( tryAxiom( theory, expSeq ) ).
      orElse( tryDef( theory, expSeq ) ).
      orElse( tryMerge( theory, expSeq ) ).
      orElse( tryWeakening( theory, expSeq ) ).
      orElse( tryNullary( theory, expSeq ) ).
      orElse( tryStrongQ( theory, expSeq ) ).
      orElse( tryWeakQ( theory, expSeq ) ).
      orElse( tryUnary( theory, expSeq, intuitionisticHeuristics ) ).
      orElse( tryCut( theory, expSeq ) ).
      orElse( tryInduction( theory, expSeq ) ).
      orElse( tryBinary( theory, expSeq, intuitionisticHeuristics ) ).
      orElse( if ( intuitionisticHeuristics ) tryIntuitionisticImpLeft( theory, expSeq ) else None ).
      orElse( if ( intuitionisticHeuristics ) tryUnary( theory, expSeq, intuitionistic = false ) else None ).
      orElse( if ( intuitionisticHeuristics ) tryBinary( theory, expSeq, intuitionistic = false ) else None ).
      orElse( tryTheory( theory, expSeq ) ).
      getOrElse( Left( theory -> expSeq ) ).
      map {
        ContractionMacroRule( _ ).
          ensuring { _.conclusion isSubsetOf expSeq.shallow }
      }
  }

  private def tryAxiom( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    val shallowSequent = expSeq.shallow
    if ( shallowSequent.isTaut )
      Some( Right( LogicalAxiom( shallowSequent.antecedent intersect shallowSequent.succedent head ) ) )
    else
      None
  }

  private def tryTheory( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    quiet( theorySolver( expSeq collect { case ETAtom( atom: Atom, _ ) => atom } ) ).map {
      Right( _ )
    }

  private def tryDef( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETDefinition( sh, ch ), i ) =>
        mapIf( solve( theory, expSeq.updated( i, ch ) ), ch.shallow, i.polarity ) {
          DefinitionRule( _, ch.shallow, sh, i.polarity )
        }
    }

  private def tryMerge( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( e @ ETMerge( a, b ), i: Ant ) => solve( theory, a +: b +: expSeq.delete( i ) )
      case ( e @ ETMerge( a, b ), i: Suc ) => solve( theory, expSeq.delete( i ) :+ a :+ b )
    }

  private def tryNullary( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETTop( _ ), i: Suc )    => Right( TopAxiom )
      case ( ETBottom( _ ), i: Ant ) => Right( BottomAxiom )
    }

  private def tryWeakening( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETWeakening( _, _ ), i ) => solve( theory, expSeq delete i )
      case ( ETTop( _ ), i: Ant )     => solve( theory, expSeq delete i )
      case ( ETBottom( _ ), i: Suc )  => solve( theory, expSeq delete i )
    }

  private def tryUnary( theory: Theory, expSeq: ExpansionSequent,
                        intuitionistic: Boolean ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements.reverseIterator collectFirst {
      case ( ETNeg( f ), i: Ant ) if !intuitionistic =>
        mapIf( solve( theory, expSeq.delete( i ) :+ f ), f.shallow, !i.polarity ) {
          NegLeftRule( _, f.shallow )
        }
      case ( ETNeg( f ), i: Suc ) if !intuitionistic || expSeq.succedent.size <= 1 =>
        mapIf( solve( theory, f +: expSeq.delete( i ) ), f.shallow, !i.polarity ) {
          NegRightRule( _, f.shallow )
        }
      case ( ETAnd( f, g ), i: Ant ) =>
        mapIf( solve( theory, f +: g +: expSeq.delete( i ) ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          AndLeftMacroRule( _, f.shallow, g.shallow )
        }
      case ( ETOr( f, g ), i: Suc ) =>
        mapIf( solve( theory, expSeq.delete( i ) :+ f :+ g ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          OrRightMacroRule( _, f.shallow, g.shallow )
        }
      case ( ETImp( f, g ), i: Suc ) if !intuitionistic || expSeq.succedent.size <= 1 =>
        mapIf( solve( theory, f +: expSeq.delete( i ) :+ g ), f.shallow, !i.polarity, g.shallow, i.polarity ) {
          ImpRightMacroRule( _, f.shallow, g.shallow )
        }
    }

  private def tryBinary( theory: Theory, expSeq: ExpansionSequent, intuitionistic: Boolean ): Option[UnprovableOrLKProof] = {
    def handle( i: SequentIndex, e: ExpansionTree, f: ExpansionTree, g: ExpansionTree,
                rule: ( LKProof, LKProof, Formula ) => LKProof ) =
      solve( theory, if ( f.polarity.inSuc ) expSeq.delete( i ) :+ f else f +: expSeq.delete( i ) ) flatMap { p1 =>
        if ( !p1.conclusion.contains( f.shallow, f.polarity ) ) Right( p1 )
        else solve( theory, if ( g.polarity.inSuc ) expSeq.delete( i ) :+ g else g +: expSeq.delete( i ) ) map { p2 =>
          if ( !p2.conclusion.contains( g.shallow, g.polarity ) ) p2
          else rule( p1, p2, e.shallow )
        }
      }

    expSeq.zipWithIndex.swapped.elements collectFirst {
      case ( e @ ETAnd( f, g ), i: Suc )                    => handle( i, e, f, g, AndRightRule( _, _, _ ) )
      case ( e @ ETOr( f, g ), i: Ant )                     => handle( i, e, f, g, OrLeftRule( _, _, _ ) )
      case ( e @ ETImp( f, g ), i: Ant ) if !intuitionistic => handle( i, e, f, g, ImpLeftRule( _, _, _ ) )
    }
  }

  private def tryIntuitionisticImpLeft( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.antecedent.view.flatMap {
      case ( e @ ETImp( f, g ), i: Ant ) =>
        val expSeq_ = Sequent( expSeq.antecedent.collect { case et @ ETAtom( _, _ ) => et }, Vector( f ) )
        solve( theory, expSeq_ ).map { p1 =>
          if ( !p1.conclusion.contains( f.shallow, f.polarity ) ) Right( p1 )
          else solve( theory, expSeq.updated( i, g ) ).map { p2 =>
            if ( !p2.conclusion.contains( g.shallow, g.polarity ) ) p2
            else ImpLeftRule( p1, p2, e.shallow )
          }
        }.right.toSeq
      case _ => Nil
    }.headOption

  private def tryStrongQ( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETStrongQuantifier( sh, ev, f ), i: Ant ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ExistsLeftRule( _, sh, ev )
        }
      case ( ETStrongQuantifier( sh, ev, f ), i: Suc ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ForallRightRule( _, sh, ev )
        }
      case ( ETSkolemQuantifier( sh, skT, f ), i: Ant ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ExistsSkLeftRule( _, sh, skT )
        }
      case ( ETSkolemQuantifier( sh, skT, f ), i: Suc ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ForallSkRightRule( _, sh, skT )
        }
    }

  private def tryWeakQ( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
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

  private def tryCut( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- theory.getExpansionTrees ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet

    theory.cuts.zipWithIndex collectFirst {
      case ( ETCut.Cut( cut1, cut2 ), i ) if freeVariables( cut1.shallow ) intersect upcomingEVs isEmpty =>
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

  private def tryInduction( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- theory.getExpansionTrees ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet

    theory.inductions.zipWithIndex.collectFirst {
      case ( ETInduction.Induction( etCases, hyps, suc ), i ) if freeVariables( hyps.shallow ) intersect upcomingEVs isEmpty =>
        val newTheory = Theory( theory.cuts, theory.inductions.zipWithIndex.filter { _._2 != i }.map { _._1 } )
        def recCases( etCases: Seq[ETInduction.Case], lkCases: Seq[InductionCase] ): UnprovableOrLKProof = {
          etCases match {
            case ETInduction.Case( c, evs, auxiliary ) +: tail =>
              solve( newTheory, expSeq ++ auxiliary ) flatMap { p =>
                if ( p.conclusion.intersect( auxiliary.shallow ).isEmpty ) Right( p )
                else {
                  val pWkn = WeakeningMacroRule( p, auxiliary.shallow, strict = false )
                  val aIdxs = auxiliary.antecedent.map( a => pWkn.conclusion.indexOf( a.shallow, Polarity.InAntecedent ) )
                  val sIdx = pWkn.conclusion.indexOf( auxiliary.succedent.head.shallow, Polarity.InSuccedent )
                  recCases( tail, InductionCase( pWkn, c, aIdxs, evs, sIdx ) +: lkCases )
                }
              }
            case Nil =>
              solve( newTheory, suc +: expSeq ) map { p =>
                if ( !p.conclusion.contains( suc.shallow, Polarity.InAntecedent ) ) p
                else {
                  val All( v, f ) = suc.shallow
                  val freshVar = Var( rename.awayFrom( freeVariables( p.conclusion ) ).fresh( v.name ), v.ty )
                  ProofBuilder
                    .c( InductionRule( lkCases.reverse, Abs( v, f ), freshVar ) )
                    .u( ForallRightRule( _, suc.shallow, freshVar ) )
                    .u( CutRule( _, p, suc.shallow ) )
                    .qed
                }
              }
          }
        }
        recCases( etCases, Seq.empty )
    }
  }

}
