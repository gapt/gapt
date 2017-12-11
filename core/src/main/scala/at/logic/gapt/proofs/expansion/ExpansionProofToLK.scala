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

  def apply( expansionProof: ExpansionProof )( implicit ctx: Context = Context() ): UnprovableOrLKProof = {

    // TODO build induction axioms from ctx
    // constructors: basecase, c1: T -> T, c2: T*T -> T, ...
    // (X(basecase) & forall x0 X(x0) -> X(c1(x0)) & forall x0,x1 (X(x0) & X(x1)) -> X(c2(x0, x1))) -> forall x X(x)
    val inductions = for {
      inductionAxiomExpansion <- expansionProof.expansionSequent.antecedent
      if inductionAxiomExpansion.shallow == ETInduction.inductionAxiom
      cut <- inductionAxiomExpansion( HOLPosition( 1 ) )
      cut1 <- cut( HOLPosition( 1 ) )
      cut2 <- cut( HOLPosition( 2 ) )
    } yield ETImp( cut1, cut2 )

    /*
    println( "inductions" )
    inductions.foreach { x => println( "induction: " + x ) }

    println( "ctx: " + ctx )
    println( "ctx constructors:\n" + ctx.get[StructurallyInductiveTypes].constructors )
    */

    solve( expansionProof.cuts, inductions, expansionProof.nonCutPart filter { x => x.shallow != ETInduction.inductionAxiom } ).
      map( WeakeningMacroRule( _, expansionProof.nonCutPart.shallow filter { x => x != ETInduction.inductionAxiom } ) )

  }

  private def solve( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): UnprovableOrLKProof = {
    None.
      orElse( tryAxiom( cuts, inductions, expSeq ) ).
      orElse( tryDef( cuts, inductions, expSeq ) ).
      orElse( tryMerge( cuts, inductions, expSeq ) ).
      orElse( tryWeakening( cuts, inductions, expSeq ) ).
      orElse( tryNullary( cuts, inductions, expSeq ) ).
      orElse( tryStrongQ( cuts, inductions, expSeq ) ).
      orElse( tryWeakQ( cuts, inductions, expSeq ) ).
      orElse( tryUnary( cuts, inductions, expSeq ) ).
      orElse( tryCut( cuts, inductions, expSeq ) ).
      orElse( tryInduction( cuts, inductions, expSeq ) ).
      orElse( tryBinary( cuts, inductions, expSeq ) ).
      orElse( tryTheory( cuts, inductions, expSeq ) ).
      getOrElse( Left( cuts -> expSeq ) ). // TODO crashes at isSubsetOf, what about inductions here?
      map {
        ContractionMacroRule( _ ).
          ensuring { _.conclusion isSubsetOf expSeq.map { _.shallow } }
      }
  }

  private def tryAxiom( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    val shallowSequent = expSeq.shallow
    if ( shallowSequent.isTaut )
      Some( Right( LogicalAxiom( shallowSequent.antecedent intersect shallowSequent.succedent head ) ) )
    else
      None
  }

  private def tryTheory( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    theorySolver( expSeq collect { case ETAtom( atom, _ ) => atom } ).map { Right( _ ) }

  private def tryDef( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETDefinition( sh, ch ), i ) =>
        mapIf( solve( cuts, inductions, expSeq.updated( i, ch ) ), ch.shallow, i.polarity ) {
          DefinitionRule( _, ch.shallow, sh, i.polarity )
        }
    }

  private def tryMerge( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( e @ ETMerge( a, b ), i: Ant ) => solve( cuts, inductions, a +: b +: expSeq.delete( i ) )
      case ( e @ ETMerge( a, b ), i: Suc ) => solve( cuts, inductions, expSeq.delete( i ) :+ a :+ b )
    }

  private def tryNullary( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETTop( _ ), i: Suc )    => Right( TopAxiom )
      case ( ETBottom( _ ), i: Ant ) => Right( BottomAxiom )
    }

  private def tryWeakening( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETWeakening( _, _ ), i ) => solve( cuts, inductions, expSeq delete i )
      case ( ETTop( _ ), i: Ant )     => solve( cuts, inductions, expSeq delete i )
      case ( ETBottom( _ ), i: Suc )  => solve( cuts, inductions, expSeq delete i )
    }

  private def tryUnary( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETNeg( f ), i: Ant ) => mapIf( solve( cuts, inductions, expSeq.delete( i ) :+ f ), f.shallow, !i.polarity ) { NegLeftRule( _, f.shallow ) }
      case ( ETNeg( f ), i: Suc ) => mapIf( solve( cuts, inductions, f +: expSeq.delete( i ) ), f.shallow, !i.polarity ) { NegRightRule( _, f.shallow ) }

      case ( e @ ETAnd( f, g ), i: Ant ) =>
        mapIf( solve( cuts, inductions, f +: g +: expSeq.delete( i ) ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          AndLeftMacroRule( _, f.shallow, g.shallow )
        }
      case ( e @ ETOr( f, g ), i: Suc ) =>
        mapIf( solve( cuts, inductions, expSeq.delete( i ) :+ f :+ g ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          OrRightMacroRule( _, f.shallow, g.shallow )
        }
      case ( e @ ETImp( f, g ), i: Suc ) =>
        mapIf( solve( cuts, inductions, f +: expSeq.delete( i ) :+ g ), f.shallow, !i.polarity, g.shallow, i.polarity ) {
          ImpRightMacroRule( _, f.shallow, g.shallow )
        }
    }

  private def tryBinary( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    def handle( i: SequentIndex, e: ExpansionTree, f: ExpansionTree, g: ExpansionTree,
                rule: ( LKProof, LKProof, Formula ) => LKProof ) =
      solve( cuts, inductions, if ( f.polarity.inSuc ) expSeq.delete( i ) :+ f else f +: expSeq.delete( i ) ) flatMap { p1 =>
        if ( !p1.conclusion.contains( f.shallow, f.polarity ) ) Right( p1 )
        else solve( cuts, inductions, if ( g.polarity.inSuc ) expSeq.delete( i ) :+ g else g +: expSeq.delete( i ) ) map { p2 =>
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

  private def tryStrongQ( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETStrongQuantifier( sh, ev, f ), i: Ant ) =>
        mapIf( solve( cuts, inductions, expSeq.updated( i, f ) ), f.shallow, i.polarity ) { ExistsLeftRule( _, sh, ev ) }
      case ( ETStrongQuantifier( sh, ev, f ), i: Suc ) =>
        mapIf( solve( cuts, inductions, expSeq.updated( i, f ) ), f.shallow, i.polarity ) { ForallRightRule( _, sh, ev ) }
      case ( ETSkolemQuantifier( sh, skT, skD, f ), i: Ant ) =>
        mapIf( solve( cuts, inductions, expSeq.updated( i, f ) ), f.shallow, i.polarity ) { ExistsSkLeftRule( _, skT, skD ) }
      case ( ETSkolemQuantifier( sh, skT, skD, f ), i: Suc ) =>
        mapIf( solve( cuts, inductions, expSeq.updated( i, f ) ), f.shallow, i.polarity ) { ForallSkRightRule( _, skT, skD ) }
    }

  private def tryWeakQ( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- cuts ++ inductions ++ expSeq.elements
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

        return Some( solve( cuts, inductions, newExpSeq ) map { p0 =>
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

  private def tryCut( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    lazy val upcomingEVs = ( for {
      et <- cuts ++ inductions ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet

    cuts.zipWithIndex collectFirst {
      case ( ETImp( cut1, cut2 ), i ) if freeVariables( cut1.shallow ) intersect upcomingEVs isEmpty =>
        val newCuts = cuts.zipWithIndex.filter { _._2 != i }.map { _._1 }
        solve( newCuts, inductions, expSeq :+ cut1 ) flatMap { p1 =>
          if ( !p1.conclusion.contains( cut1.shallow, Polarity.InSuccedent ) ) Right( p1 )
          else solve( newCuts, inductions, cut2 +: expSeq ) map { p2 =>
            if ( !p2.conclusion.contains( cut2.shallow, Polarity.InAntecedent ) ) p2
            else CutRule( p1, p2, cut1.shallow )
          }
        }
    }
  }

  private def tryInduction( cuts: Seq[ETImp], inductions: Seq[ETImp], expSeq: ExpansionSequent )( implicit ctx: Context ): Option[UnprovableOrLKProof] = {
    val upcomingEVs = ( for {
      et <- cuts ++ inductions ++ expSeq.elements
      ETStrongQuantifier( _, ev, _ ) <- et.subProofs
    } yield ev ).toSet

    inductions.zipWithIndex.collectFirst {
      // TODO handle more than 2 conjuncts with more constructors
      case ( ETImp( ant @ ETAnd( ant1, ETStrongQuantifier( _, ev, ETImp( ch1, ch2 ) ) ), suc ), i ) if freeVariables( ant.shallow ) intersect upcomingEVs isEmpty =>
        val newInductions = inductions.zipWithIndex.filter { _._2 != i }.map { _._1 }

        // TODO: recurse over ant
        val ret = solve( cuts, newInductions, expSeq :+ ant1 ) flatMap { p1 =>
          if ( !p1.conclusion.contains( ant1.shallow, Polarity.InSuccedent ) ) Right( p1 )
          else solve( cuts, newInductions, ch1 +: expSeq :+ ch2 ) map { p2 =>
            if ( !p2.conclusion.contains( ch1.shallow, Polarity.InAntecedent )
              || !p2.conclusion.contains( ch2.shallow, Polarity.InSuccedent ) ) p2
            else {
              val index1 = p1.conclusion.indexOf( ant1.shallow, Polarity.InSuccedent )
              val index2 = p2.conclusion.indexOf( ch1.shallow, Polarity.InAntecedent )
              val index3 = p2.conclusion.indexOf( ch2.shallow, Polarity.InSuccedent )
              val cases = Seq(
                InductionCase( p1, hoc"0:nat", Seq.empty, Seq.empty, index1 ),
                InductionCase( p2, hoc"s:nat>nat", Seq( index2 ), Seq( ev ), index3 ) )
              val App( _, qfFormula @ Abs( v, _ ) ) = suc.shallow

              InductionRule( cases, qfFormula, v )
            }
          }
        }
        ret
    }

  }

}
