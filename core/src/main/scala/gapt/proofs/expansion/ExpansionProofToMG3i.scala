package gapt.proofs.expansion

import gapt.proofs.lk._
import gapt.proofs._
import gapt.expr._
import gapt.provers.escargot.Escargot
import gapt.utils.quiet
import ExpansionProofToLK._
import gapt.expr.hol.instantiate
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext

import scala.collection.mutable

object ExpansionProofToMG3i {
  def apply( expansionProof: ExpansionProof )( implicit ctx: Context = MutableContext.guess( expansionProof.deep ) ): Either[( Theory, ExpansionSequent ), LKProof] =
    new ExpansionProofToMG3i( Escargot.getAtomicLKProof )( ctx.newMutable ).apply( expansionProof )
}

class ExpansionProofToMG3i( theorySolver: HOLClause => Option[LKProof] )( implicit ctx: MutableContext ) extends SolveUtils {
  type Error = ( Theory, ExpansionSequent )

  def apply( expansionProof: ExpansionProof ): UnprovableOrLKProof =
    solve( Theory( expansionProof.cuts, expansionProof.inductions ), expansionProof.nonTheoryPart ).
      map( WeakeningMacroRule( _, expansionProof.nonTheoryPart.shallow ) ).
      map( eliminateDefinitions( newDefs.toMap )( _ ) )

  val newDefs = mutable.Map[Const, Expr]()
  def mkAbbrAtom( f: Formula ): Atom = {
    val fvs = freeVariables( f ).toSeq
    val what = Abs( fvs, f )
    val by = ctx.addDefinition( what )
    newDefs( by ) = what
    by( fvs ).asInstanceOf[Atom]
  }

  private def solve( theory: Theory, expSeq: ExpansionSequent ): UnprovableOrLKProof = {
    None.
      orElse( tryAxiom( theory, expSeq ) ).
      orElse( tryDef( theory, expSeq ) ).
      orElse( tryMerge( theory, expSeq ) ).
      orElse( tryWeakening( theory, expSeq ) ).
      orElse( tryNullary( theory, expSeq ) ).
      orElse( tryInvStrongQ( theory, expSeq ) ).
      orElse( tryWeakQ( theory, expSeq ) ).
      orElse( tryInvUnary( theory, expSeq ) ).
      orElse( tryInvBinary( theory, expSeq ) ).
      orElse( trySimpNegL( theory, expSeq ) ).
      orElse( trySimpImpL( theory, expSeq ) ).
      orElse( tryPropag( theory, expSeq ) ).
      orElse( tryNonInv( theory, expSeq ) ).
      orElse( tryCut( theory, expSeq ) ).
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
    quiet( theorySolver( expSeq collect { case ETAtom( atom, _ ) => atom } ) ).map {
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
      case ( ETMerge( a, b ), i: Ant ) => solve( theory, a +: b +: expSeq.delete( i ) )
      case ( ETMerge( a, b ), i: Suc ) => solve( theory, expSeq.delete( i ) :+ a :+ b )
    }

  private def tryNullary( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETTop( _ ), _: Suc )    => Right( TopAxiom )
      case ( ETBottom( _ ), _: Ant ) => Right( BottomAxiom )
    }

  private def tryWeakening( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETWeakening( _, _ ), i ) => solve( theory, expSeq delete i )
      case ( ETTop( _ ), i: Ant )     => solve( theory, expSeq delete i )
      case ( ETBottom( _ ), i: Suc )  => solve( theory, expSeq delete i )
    }

  private def tryInvUnary( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETAnd( f, g ), i: Ant ) =>
        mapIf( solve( theory, f +: g +: expSeq.delete( i ) ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          AndLeftMacroRule( _, f.shallow, g.shallow )
        }
      case ( ETOr( f, g ), i: Suc ) =>
        mapIf( solve( theory, expSeq.delete( i ) :+ f :+ g ), f.shallow, i.polarity, g.shallow, i.polarity ) {
          OrRightMacroRule( _, f.shallow, g.shallow )
        }
    }

  private def isCopy( e: ExpansionTree ): Boolean =
    e match {
      case ETTop( _ )     => true
      case ETBottom( _ )  => true
      case ETAtom( _, _ ) => true
      case _              => false
    }

  private def trySimpNegL( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETNeg( ETTop( _ ) ), _: Ant )    => Right( NegLeftRule( TopAxiom, Top() ) )
      case ( ETNeg( ETBottom( _ ) ), _: Suc ) => Right( NegRightRule( BottomAxiom, Bottom() ) )
      case ( ETNeg( ETBottom( _ ) ), i: Ant ) => solve( theory, expSeq.delete( i ) )
      case ( ETNeg( ETTop( _ ) ), i: Suc )    => solve( theory, expSeq.delete( i ) )
      case ( ETNeg( ETNeg( f ) ), i: Ant ) if expSeq.succedent.isEmpty =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, f.polarity ) {
          ProofBuilder.c( _ ).
            u( NegRightRule( _, f.shallow ) ).
            u( NegLeftRule( _, -f.shallow ) ).
            qed
        }
      case ( ETNeg( ETAnd( f, g ) ), i: Ant ) =>
        val h = ETImp( f, ETNeg( g ) )
        mapIf( solve( theory, ETImp( f, ETNeg( g ) ) +: expSeq.delete( i ) ), h.shallow, h.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( f.shallow ) ).
            c( LogicalAxiom( g.shallow ) ).
            b( AndRightRule( _, _, f.shallow & g.shallow ) ).
            u( NegLeftRule( _, f.shallow & g.shallow ) ).
            u( NegRightRule( _, g.shallow ) ).
            u( ImpRightRule( _, h.shallow ) ).
            c( _ ).
            b( CutRule( _, _, h.shallow ) ).
            qed
        }
      case ( ETNeg( ETOr( f, g ) ), i: Ant ) =>
        mapIf(
          solve( theory, ETNeg( f ) +: ETNeg( g ) +: expSeq.delete( i ) ),
          -f.shallow, !f.polarity, -g.shallow, !g.polarity ) {
            ProofBuilder.
              c( LogicalAxiom( f.shallow ) ).
              u( WeakeningRightRule( _, g.shallow ) ).
              u( OrRightRule( _, f.shallow, g.shallow ) ).
              u( NegLeftRule( _, f.shallow | g.shallow ) ).
              u( NegRightRule( _, f.shallow ) ).
              c( LogicalAxiom( g.shallow ) ).
              u( WeakeningRightRule( _, f.shallow ) ).
              u( OrRightRule( _, f.shallow, g.shallow ) ).
              u( NegLeftRule( _, f.shallow | g.shallow ) ).
              u( NegRightRule( _, g.shallow ) ).
              c( _ ).
              u( WeakeningMacroRule( _, -f.shallow +: -g.shallow +: Sequent(), strict = false ) ).
              b( CutRule( _, _, -g.shallow ) ).
              b( CutRule( _, _, -f.shallow ) ).
              qed
          }
      case ( ETNeg( f @ ( ETImp( _, _ ) | ETStrongQuantifier( _, _, _ ) | ETNeg( _ ) ) ), i: Ant ) =>
        val h = ETImp( f, ETBottom( Polarity.InAntecedent ) )
        mapIf( solve( theory, h +: expSeq.delete( i ) ), h.shallow, h.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( f.shallow ) ).
            u( NegLeftRule( _, f.shallow ) ).
            u( WeakeningRightRule( _, Bottom() ) ).
            u( ImpRightRule( _, h.shallow ) ).
            c( _ ).
            b( CutRule( _, _, h.shallow ) ).
            qed
        }
      case ( ETNeg( ETWeakQuantifier( Ex( x, sh ), insts ) ), i: Ant ) =>
        val h = ETWeakQuantifier( All( x, -sh ), for ( ( i, f ) <- insts ) yield i -> ETNeg( f ) )
        mapIf( solve( theory, expSeq.updated( i, h ) ), h.shallow, h.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( sh ) ).
            u( ExistsRightRule( _, Ex( x, sh ), x ) ).
            u( NegLeftRule( _, Ex( x, sh ) ) ).
            u( NegRightRule( _, sh ) ).
            u( ForallRightRule( _, All( x, -sh ) ) ).
            c( _ ).
            b( CutRule( _, _, h.shallow ) ).
            qed
        }
    }

  private def trySimpImpL( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETImp( ETBottom( _ ), _ ), i: Ant ) => solve( theory, expSeq.delete( i ) )
      case ( ETImp( ETTop( _ ), f ), i: Ant ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, f.polarity ) {
          ImpLeftRule( TopAxiom, _, Top() --> f.shallow )
        }
      case ( ETImp( ETAnd( f, g ), h ), i: Ant ) =>
        val e = ETImp( f, ETImp( g, h ) )
        mapIf( solve( theory, expSeq.updated( i, e ) ), e.shallow, e.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( f.shallow ) ).
            c( LogicalAxiom( g.shallow ) ).
            b( AndRightRule( _, _, f.shallow & g.shallow ) ).
            c( LogicalAxiom( h.shallow ) ).
            b( ImpLeftRule( _, _, ( f.shallow & g.shallow ) --> h.shallow ) ).
            u( ImpRightRule( _, g.shallow --> h.shallow ) ).
            u( ImpRightRule( _, e.shallow ) ).
            c( _ ).
            b( CutRule( _, _, e.shallow ) ).
            qed
        }
      case ( f0 @ ETImp( ETImp( f, g ), h ), i: Ant ) if !isCopy( g ) =>
        val g_ = mkAbbrAtom( g.shallow )
        val e1 = ETDefinition( f0.shallow, ETImp( ETImp( f, ETAtom( g_, Polarity.InSuccedent ) ), h ) )
        val e2 = ETDefinition( g.shallow --> g.shallow, ETImp( g, ETAtom( g_, Polarity.InAntecedent ) ) )
        mapIf( solve( theory, e1 +: e2 +: expSeq.delete( i ) ), e2.shallow, e2.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( g.shallow ) ).
            u( ImpRightRule( _, e2.shallow ) ).
            c( _ ).
            b( CutRule( _, _, e2.shallow ) ).
            qed
        }
      case ( f @ ETImp( g @ ( ETOr( _, _ ) | ETWeakQuantifier( _, _ ) ), h ), i: Ant ) if !isCopy( h ) =>
        val h_ = mkAbbrAtom( h.shallow )
        val e1 = ETDefinition( f.shallow, ETImp( g, ETAtom( h_, Polarity.InAntecedent ) ) )
        val e2 = ETDefinition( h.shallow --> h.shallow, ETImp( ETAtom( h_, Polarity.InSuccedent ), h ) )
        mapIf( solve( theory, e1 +: e2 +: expSeq.delete( i ) ), e2.shallow, e2.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( h.shallow ) ).
            u( ImpRightRule( _, e2.shallow ) ).
            c( _ ).
            b( CutRule( _, _, e2.shallow ) ).
            qed
        }
      case ( f0 @ ETImp( ETOr( f, g ), h ), i: Ant ) if isCopy( h ) =>
        val e1 = ETImp( f, h )
        val e2 = ETImp( g, h )
        mapIf( solve( theory, e1 +: e2 +: expSeq.delete( i ) ), e1.shallow, e1.polarity, e2.shallow, e2.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( f.shallow ) ).
            u( WeakeningRightRule( _, g.shallow ) ).
            u( OrRightRule( _, f.shallow, g.shallow ) ).
            c( LogicalAxiom( h.shallow ) ).
            b( ImpLeftRule( _, _, f0.shallow ) ).
            u( ImpRightRule( _, e1.shallow ) ).
            c( LogicalAxiom( g.shallow ) ).
            u( WeakeningRightRule( _, f.shallow ) ).
            u( OrRightRule( _, f.shallow, g.shallow ) ).
            c( LogicalAxiom( h.shallow ) ).
            b( ImpLeftRule( _, _, f0.shallow ) ).
            u( ImpRightRule( _, e2.shallow ) ).
            c( _ ).
            u( WeakeningMacroRule( _, e1.shallow +: e2.shallow +: Sequent(), strict = false ) ).
            b( CutRule( _, _, e2.shallow ) ).
            b( CutRule( _, _, e1.shallow ) ).
            qed
        }
      case ( ETImp( ETWeakQuantifier( sh0 @ Ex( x0, _ ), insts ), g ), i: Ant ) if isCopy( g ) =>
        val x = rename( x0, freeVariables( g.shallow ) )
        val sh = instantiate( sh0, x )
        val h = ETWeakQuantifier( All( x, sh --> g.shallow ), for ( ( i, e ) <- insts ) yield i -> ETImp( e, g ) )
        mapIf( solve( theory, expSeq.updated( i, h ) ), h.shallow, h.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( sh ) ).
            u( ExistsRightRule( _, Ex( x, sh ), x ) ).
            c( LogicalAxiom( g.shallow ) ).
            b( ImpLeftRule( _, _, Ex( x, sh ) --> g.shallow ) ).
            u( ImpRightRule( _, sh, g.shallow ) ).
            u( ForallRightRule( _, All( x, sh --> g.shallow ) ) ).
            c( _ ).
            b( CutRule( _, _, h.shallow ) ).
            qed
        }
      case ( f0 @ ETImp( ETNeg( f ), g ), i: Ant ) =>
        val h = ETImp( ETImp( f, ETBottom( Polarity.InSuccedent ) ), g )
        mapIf( solve( theory, expSeq.updated( i, h ) ), h.shallow, h.polarity ) {
          ProofBuilder.
            c( LogicalAxiom( f.shallow ) ).
            c( BottomAxiom ).
            b( ImpLeftRule( _, _, f.shallow --> Bottom() ) ).
            u( NegRightRule( _, f.shallow ) ).
            c( LogicalAxiom( g.shallow ) ).
            b( ImpLeftRule( _, _, f0.shallow ) ).
            u( ImpRightRule( _, h.shallow ) ).
            c( _ ).
            b( CutRule( _, _, h.shallow ) ).
            qed
        }
    }

  private def solveAtomic( clause: HOLClause ): Option[LKProof] =
    clause.antecedent.intersect( clause.succedent ).headOption.
      map( LogicalAxiom ).
      orElse( theorySolver( clause ) )

  private def tryPropag( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    lazy val antClause = Sequent( expSeq.shallow.antecedent.collect { case a: Atom => a }, Vector() )
    expSeq.zipWithIndex.elements.view.flatMap {
      case ( ETImp( ETAtom( f, _ ), g ), i: Ant ) =>
        solveAtomic( antClause :+ f ).map { p1 =>
          if ( !p1.conclusion.succedent.contains( f ) ) Right( p1 )
          else mapIf( solve( theory, expSeq.updated( i, g ) ), g.shallow, g.polarity ) { p2 =>
            ImpLeftRule( p1, p2, f --> g.shallow )
          }
        }
      case ( ETNeg( ETAtom( f, _ ) ), _: Ant ) =>
        solveAtomic( antClause :+ f ).map { p1 =>
          Right( if ( !p1.conclusion.succedent.contains( f ) ) p1
          else NegLeftRule( p1, f ) )
        }
      case _ => None
    }.headOption
  }

  private def tryInvBinary( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
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
      case ( e @ ETAnd( f, g ), i: Suc ) => handle( i, e, f, g, AndRightRule( _, _, _ ) )
      case ( e @ ETOr( f, g ), i: Ant )  => handle( i, e, f, g, OrLeftRule( _, _, _ ) )
    }
  }

  private def tryNonInv( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] = {
    def invIfSucc1( x: UnprovableOrLKProof ): Option[UnprovableOrLKProof] =
      if ( expSeq.succedent.size <= 1 ) Some( x )
      else x.toOption.map( Right( _ ) )
    expSeq.zipWithIndex.elements.view.flatMap {
      case ( ETNeg( f ), _: Suc ) =>
        invIfSucc1( mapIf( solve( theory, f +: expSeq.antecedent ++: Sequent() ), f.shallow, f.polarity ) {
          NegRightRule( _, f.shallow )
        } )
      case ( ETImp( f, g ), _: Suc ) =>
        invIfSucc1( mapIf( solve( theory, f +: expSeq.antecedent ++: Sequent() :+ g ), f.shallow, f.polarity, g.shallow, g.polarity ) {
          ImpRightMacroRule( _, f.shallow, g.shallow )
        } )
      case ( ETStrongQuantifier( sh, ev, f ), i: Suc ) =>
        invIfSucc1( mapIf( solve( theory, expSeq.antecedent ++: Sequent() :+ f ), f.shallow, i.polarity ) {
          ForallRightRule( _, sh, ev )
        } )
      case ( f0 @ ETImp( ETStrongQuantifier( All( x, sh ), ev, f ), g ), i: Ant ) =>
        solve( theory, expSeq.delete( i ).antecedent ++: Sequent() :+ f ) match {
          case Right( p1 ) if p1.endSequent.succedent.isEmpty => Some( Right( p1 ) )
          case Right( p1 ) =>
            Some( mapIf( solve( theory, g +: expSeq.delete( i ) ), g.shallow, g.polarity ) { p2 =>
              ProofBuilder.
                c( p1 ).
                u( ForallRightRule( _, All( x, sh ), ev ) ).
                c( p2 ).
                b( ImpLeftRule( _, _, f0.shallow ) ).
                qed
            } )
          case Left( _ ) => None
        }
      case ( ETImp( ETImp( f, g ), h ), i: Ant ) if isCopy( g ) =>
        solve( theory, f +: ETImp( g, h ) +: expSeq.delete( i ).antecedent ++: Sequent() :+ g ) match {
          case Right( p1 ) if p1.endSequent isSubsetOf expSeq.shallow => Some( Right( p1 ) )
          case Right( p1 ) =>
            Some( mapIf( solve( theory, h +: expSeq.delete( i ) ), h.shallow, h.polarity ) { p2 =>
              ProofBuilder.
                c( LogicalAxiom( g.shallow ) ).
                u( WeakeningLeftRule( _, f.shallow ) ).
                u( ImpRightRule( _, f.shallow --> g.shallow ) ).
                c( LogicalAxiom( h.shallow ) ).
                b( ImpLeftRule( _, _, ( f.shallow --> g.shallow ) --> h.shallow ) ).
                u( ImpRightRule( _, g.shallow --> h.shallow ) ).
                c( p1 ).
                u( WeakeningMacroRule( _, f.shallow +: ( g.shallow --> h.shallow ) +: Sequent() :+ g.shallow,
                  strict = false ) ).
                b( CutRule( _, _, g.shallow --> h.shallow ) ).
                u( ImpRightRule( _, f.shallow --> g.shallow ) ).
                c( p2 ).
                b( ImpLeftRule( _, _, ( f.shallow --> g.shallow ) --> h.shallow ) ).
                qed
            } )
          case Left( _ ) => None
        }
      case _ => None
    }.headOption
  }

  private def tryInvStrongQ( theory: Theory, expSeq: ExpansionSequent ): Option[UnprovableOrLKProof] =
    expSeq.zipWithIndex.elements collectFirst {
      case ( ETStrongQuantifier( sh, ev, f ), i: Ant ) =>
        mapIf( solve( theory, expSeq.updated( i, f ) ), f.shallow, i.polarity ) {
          ExistsLeftRule( _, sh, ev )
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

  // TODO: induction

}
