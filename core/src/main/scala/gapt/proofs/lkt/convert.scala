package gapt.proofs.lkt

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Imp
import gapt.expr.formula.Or
import gapt.expr.subst.Substitution
import gapt.logic.Polarity
import gapt.proofs.Sequent
import gapt.proofs.lk
import gapt.proofs.lk.rules
import gapt.proofs.lk.rules
import gapt.proofs.lk.rules
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BinaryLKProof
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.ContractionRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.EqualityRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.SkolemQuantifierRule
import gapt.proofs.lk.rules.StrongQuantifierRule
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.UnaryLKProof
import gapt.proofs.lk.rules.WeakQuantifierRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import lk.LKProof

trait FreshHyp {
  private var idx = 0

  def fresh( pol: Polarity ): Hyp = {
    idx += 1
    if ( pol.inSuc ) Hyp( idx ) else Hyp( -idx )
  }
  def freshAnt() = fresh( Polarity.InAntecedent )
  def freshSuc() = fresh( Polarity.InSuccedent )

  def markUsed( h: Hyp ): Unit = idx = math.max( idx, math.abs( h.idx ) + 1 )
  def markUsed( p: LKt ): Unit = p.containedHyps.foreach( markUsed )
}

class LKToLKt( debugging: Boolean ) extends FreshHyp {
  def go( p: lk.LKProof, hyps: Sequent[Hyp] ): LKt = {
    val result = p match {
      case p: ContractionRule                       => go( p.subProof, p.getSequentConnector.parent( hyps ) )
      case p @ lk.rules.WeakeningLeftRule( p1, _ )  => go( p1, p.getSequentConnector.parent( hyps ) )
      case p @ lk.rules.WeakeningRightRule( p1, _ ) => go( p1, p.getSequentConnector.parent( hyps ) )
      case p @ lk.rules.CutRule( p1, _, p2, _ ) =>
        val aux1 = freshSuc()
        val aux2 = freshAnt()
        Cut(
          p.cutFormula,
          Bound1( aux1, go( p1, p.getLeftSequentConnector.parent( hyps, aux1 ) ) ),
          Bound1( aux2, go( p2, p.getRightSequentConnector.parent( hyps, aux2 ) ) ) )
      case lk.rules.LogicalAxiom( _ )     => Ax( hyps.antecedent.head, hyps.succedent.head )
      case lk.rules.ReflexivityAxiom( _ ) => Rfl( hyps.succedent.head )
      case rules.TopAxiom                 => TopR( hyps.succedent.head )
      case BottomAxiom                    => TopR( hyps.antecedent.head )
      case p @ lk.rules.NegRightRule( p1, a1 ) =>
        val aux = freshAnt()
        NegR( hyps( p.mainIndices.head ), Bound1(
          aux,
          go( p1, p.getSequentConnector.parent( hyps ).updated( a1, aux ) ) ) )
      case p @ lk.rules.NegLeftRule( p1, a1 ) =>
        val aux = freshSuc()
        NegL( hyps( p.mainIndices.head ), Bound1(
          aux,
          go( p1, p.getSequentConnector.parent( hyps ).updated( a1, aux ) ) ) )
      case p: BinaryLKProof =>
        val hyp = hyps( p.mainIndices.head )
        val Seq( Seq( a1 ), Seq( a2 ) ) = p.auxIndices
        val aux1 = fresh( a1.polarity )
        val aux2 = fresh( a2.polarity )
        val b1 = Bound1( aux1, go( p.leftSubProof, p.getLeftSequentConnector.parent( hyps ).updated( a1, aux1 ) ) )
        val b2 = Bound1( aux2, go( p.rightSubProof, p.getRightSequentConnector.parent( hyps ).updated( a2, aux2 ) ) )
        p match {
          case lk.rules.AndRightRule( _, _, _, _ ) | lk.rules.OrLeftRule( _, _, _, _ ) | lk.rules.ImpLeftRule( _, _, _, _ ) =>
            AndR( hyp, b1, b2 )
        }
      case p: EqualityRule =>
        val main = hyps( p.auxInConclusion )
        val aux = fresh( main.polarity )
        val eq = hyps( p.eqInConclusion )
        Eql( main, eq, !p.leftToRight, p.replacementContext, Bound1(
          aux,
          go( p.subProof, p.getSequentConnector.parents( hyps ).map( _.head ).
            updated( p.aux, aux ).updated( p.eq, eq ) ) ) )
      case p: UnaryLKProof if p.auxIndices.head.size == 2 =>
        val Seq( a1, a2 ) = p.auxIndices.head
        val aux1 = fresh( a1.polarity )
        val aux2 = fresh( a2.polarity )
        val b = Bound2( aux1, aux2,
          go(
            p.subProof,
            p.getSequentConnector.parent( hyps ).updated( a1, aux1 ).updated( a2, aux2 ) ) )
        val main = hyps( p.mainIndices.head )
        p match {
          case lk.rules.AndLeftRule( _, _, _ ) | lk.rules.OrRightRule( _, _, _ ) | lk.rules.ImpRightRule( _, _, _ ) =>
            AndL( main, b )
        }
      case p @ WeakQuantifierRule( p1, a1, _, t, _, isEx ) =>
        val aux = fresh( if ( isEx ) Polarity.InSuccedent else Polarity.InAntecedent )
        AllL( hyps( p.mainIndices.head ), t, Bound1(
          aux,
          go( p1, p.getSequentConnector.parent( hyps ).updated( a1, aux ) ) ) )
      case p @ StrongQuantifierRule( p1, a1, ev, _, isAll ) =>
        val aux = fresh( if ( isAll ) Polarity.InSuccedent else Polarity.InAntecedent )
        AllR( hyps( p.mainIndices.head ), ev, Bound1(
          aux,
          go( p1, p.getSequentConnector.parent( hyps ).updated( a1, aux ) ) ) )
      case p: SkolemQuantifierRule =>
        val aux = fresh( p.aux.polarity )
        AllSk( hyps( p.mainIndices.head ), p.skolemTerm, Bound1(
          aux,
          go( p.subProof, p.getSequentConnector.parent( hyps ).updated( p.aux, aux ) ) ) )
      case p: ConversionRule =>
        val aux = fresh( p.aux.polarity )
        Def( hyps( p.mainIndices.head ), p.auxFormula, Bound1(
          aux,
          go( p.subProof, p.getSequentConnector.parent( hyps ).updated( p.aux, aux ) ) ) )
      case p: InductionRule =>
        Ind( hyps( p.mainIndices.head ), p.formula, p.term,
          p.cases.zipWithIndex.toList.map {
            case ( c, i ) =>
              val goal = freshSuc()
              val ihs = for ( h <- c.hypotheses.toList ) yield fresh( h.polarity )
              IndCase( c.constructor, c.eigenVars.toList, BoundN(
                goal +: ihs,
                go(
                  c.proof,
                  p.occConnectors( i ).parent( hyps ).
                    updated( ( c.conclusion -> goal ) +: c.hypotheses.zip( ihs ) ) ) ) )
          } )
      case lk.rules.ProofLink( refProof, _ ) =>
        Link( hyps.elements.toList, refProof )
    }
    if ( debugging ) check( result, LocalCtx( hyps.zip( p.endSequent ).elements.toMap, Substitution() ) )
    result
  }
}

object LKToLKt {
  def apply( p: LKProof, debugging: Boolean = false ): ( LKt, LocalCtx ) = {
    val conv = new LKToLKt( debugging )
    val hyps = p.endSequent.indicesSequent.map( i => conv.fresh( i.polarity ) )
    conv.go( p, hyps ) -> LocalCtx( hyps.zip( p.endSequent ).elements.toMap, Substitution() )
  }

  def forLCtx( p: LKProof, lctx: LocalCtx, debugging: Boolean = false ) = {
    val conv = new LKToLKt( debugging )
    lctx.hyps.keys.foreach( conv.markUsed )
    val hyps = for ( ( f, i ) <- p.endSequent.zipWithIndex )
      yield lctx.hyps.collectFirst { case ( h, g ) if f == g && h.polarity == i.polarity => h }.get
    conv.go( p, hyps )
  }
}

object LKtToLK {
  import gapt.proofs.lk

  private def down( p: LKProof, s: Sequent[Hyp], main: Hyp ): ( LKProof, Sequent[Hyp] ) =
    p -> p.occConnectors.head.child( s, main ).updated( p.mainIndices.head, main )
  private def down( r: LKProof, s1: Sequent[Hyp], s2: Sequent[Hyp], main: Hyp ): ( LKProof, Sequent[Hyp] ) =
    r -> r.occConnectors.head.children( s1 ).zip( r.occConnectors( 1 ).children( s2 ) ).
      map { case ( cs1, cs2 ) => ( cs1.view ++ cs2 ).head }.
      updated( r.mainIndices.head, main )

  private def withMap( b: Bound1, lctx: LocalCtx ): ( LKProof, Sequent[Hyp] ) = withMap( b.p, lctx, b.aux )
  private def withMap( b: Bound2, lctx: LocalCtx ): ( LKProof, Sequent[Hyp] ) = withMap( b.p, lctx, b.aux1, b.aux2 )
  private def withMap( b: BoundN, lctx: LocalCtx ): ( LKProof, Sequent[Hyp] ) = withMap( b.p, lctx, b.auxs: _* )
  private def withMap( p: LKt, lctx: LocalCtx, toBeWeakenedIn: Hyp* ): ( LKProof, Sequent[Hyp] ) =
    toBeWeakenedIn match {
      case h +: hs =>
        val ( r1, s1 ) = withMap( p, lctx, hs: _* )
        if ( s1.contains( h ) ) ( r1, s1 ) else {
          val r2 = if ( h.inAnt ) WeakeningLeftRule( r1, lctx( h ) ) else WeakeningRightRule( r1, lctx( h ) )
          down( r2, s1, h )
        }
      case Seq() => withMap( p, lctx )
    }

  private def contract( res: ( LKProof, Sequent[Hyp] ) ): ( LKProof, Sequent[Hyp] ) = {
    val ( r1, s1 ) = res
    s1.elements.diff( s1.elements.distinct ).headOption match {
      case Some( dup ) =>
        val Seq( a1, a2, _* ) = s1.indicesWhere( _ == dup )
        val r2 = if ( dup.inAnt ) ContractionLeftRule( r1, a1, a2 )
        else ContractionRightRule( r1, a1, a2 )
        contract( down( r2, s1, dup ) )
      case None => res
    }
  }

  def withMap( p: LKt, lctx: LocalCtx ): ( LKProof, Sequent[Hyp] ) =
    contract( p match {
      case Cut( _, q1, q2 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        val ( r2, s2 ) = withMap( q2, lctx.up2( p ) )
        val r = CutRule( r1, s1.indexOf( q1.aux ), r2, s2.indexOf( q2.aux ) )
        r -> r.getLeftSequentConnector.children( s1 ).zip( r.getRightSequentConnector.children( s2 ) ).
          map { case ( cs1, cs2 ) => ( cs1 ++ cs2 ).head }
      case Ax( main1, main2 ) => ( LogicalAxiom( lctx( main1 ) ), main1 +: Sequent() :+ main2 )
      case Rfl( main ) =>
        val Eq( t, _ ) = lctx( main )
        ( ReflexivityAxiom( t ), Sequent() :+ main )
      case TopR( main ) =>
        if ( main.inAnt )
          ( rules.BottomAxiom, main +: Sequent() )
        else
          ( TopAxiom, Sequent() :+ main )
      case NegR( main, q1 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        down( NegRightRule( r1, s1.indexOf( q1.aux ) ), s1, main )
      case NegL( main, q1 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        down( NegLeftRule( r1, s1.indexOf( q1.aux ) ), s1, main )
      case AndR( main, q1, q2 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        val ( r2, s2 ) = withMap( q2, lctx.up2( p ) )
        val r = lctx( main ) match {
          case And( _, _ ) => AndRightRule( r1, s1.indexOf( q1.aux ), r2, s2.indexOf( q2.aux ) )
          case Or( _, _ )  => OrLeftRule( r1, s1.indexOf( q1.aux ), r2, s2.indexOf( q2.aux ) )
          case Imp( _, _ ) => ImpLeftRule( r1, s1.indexOf( q1.aux ), r2, s2.indexOf( q2.aux ) )
        }
        down( r, s1, s2, main )
      case AndL( main, q1 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        val r = lctx( main ) match {
          case And( _, _ ) => AndLeftRule( r1, s1.indexOf( q1.aux1 ), s1.indexOf( q1.aux2 ) )
          case Or( _, _ )  => OrRightRule( r1, s1.indexOf( q1.aux1 ), s1.indexOf( q1.aux2 ) )
          case Imp( _, _ ) => ImpRightRule( r1, s1.indexOf( q1.aux1 ), s1.indexOf( q1.aux2 ) )
        }
        down( r, s1, main )
      case AllL( main, term, q1 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        val r = lctx( main ) match {
          case All( _, _ ) => lk.rules.ForallLeftRule( r1, s1.indexOf( q1.aux ), lctx( main ), lctx.subst( term ) )
          case Ex( _, _ )  => lk.rules.ExistsRightRule( r1, s1.indexOf( q1.aux ), lctx( main ), lctx.subst( term ) )
        }
        down( r, s1, main )
      case AllR( main, ev0, q1 ) =>
        val lctx1 = lctx.up1( p )
        val ( r1, s1 ) = withMap( q1, lctx1 )
        val ev = lctx1.subst( ev0 ).asInstanceOf[Var]
        val r = lctx( main ) match {
          case All( _, _ ) => lk.rules.ForallRightRule( r1, s1.indexOf( q1.aux ), lctx( main ), ev )
          case Ex( _, _ )  => lk.rules.ExistsLeftRule( r1, s1.indexOf( q1.aux ), lctx( main ), ev )
        }
        down( r, s1, main )
      case Eql( main, eq, ltr, rwCtx0, q1 ) if q1.aux == eq =>
        withMap( Eql( main, eq, ltr, rwCtx0, q1.rename( Seq( eq ) ) ), lctx )
      case Eql( main, eq, _, rwCtx0, q1 ) =>
        val ( r1, s1 ) = withMap( q1.p, lctx.up1( p ), q1.aux )
        val r2 = rules.WeakeningLeftRule( r1, lctx( eq ) )
        val s2 = r2.getSequentConnector.child( s1, eq )
        val rwCtx = lctx.subst( rwCtx0 )
        val r =
          if ( main.inAnt ) EqualityLeftRule( r2, s2.indexOf( eq ), s2.indexOf( q1.aux ), rwCtx.asInstanceOf[Abs] )
          else EqualityRightRule( r2, s2.indexOf( eq ), s2.indexOf( q1.aux ), rwCtx.asInstanceOf[Abs] )
        r -> r.getSequentConnector.child( s2, main ).updated( r.eqInConclusion, eq ).updated( r.auxInConclusion, main )
      case Def( main, _, q1 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        down( lk.rules.ConversionRule( r1, s1.indexOf( q1.aux ), lctx( main ) ), s1, main )
      case AllSk( main, term, q1 ) =>
        val ( r1, s1 ) = withMap( q1, lctx.up1( p ) )
        val r2 = lctx( main ) match {
          case All( _, _ ) => ForallSkRightRule( r1, s1.indexOf( q1.aux ), lctx( main ), term )
          case Ex( _, _ )  => ExistsSkLeftRule( r1, s1.indexOf( q1.aux ), lctx( main ), term )
        }
        down( r2, s1, main )
      case Ind( main, f0, t0, cases ) =>
        val ( rs, ss ) = cases.zipWithIndex.map {
          case ( IndCase( ctr, evs0, q ), i ) =>
            val lctxn = lctx.upn( p, i )
            val evs = evs0.map( lctxn.subst( _ ).asInstanceOf[Var] )
            val ( r1, s1 ) = withMap( q, lctxn )
            val goal +: ihs = q.auxs
            InductionCase( r1, ctr, ihs.map( s1.indexOf ), evs, s1.indexOf( goal ) ) -> s1
        }.unzip
        val f = lctx.subst( f0 ).asInstanceOf[Abs]
        val t = lctx.subst( t0 )
        val r2 = InductionRule( rs, f, t )
        val s2 = r2.endSequent.indicesSequent.map( i =>
          if ( i == r2.mainIndices.head ) main
          else ss.zipWithIndex.flatMap { case ( s, j ) => r2.occConnectors( j ).parentOption( i ).map( s( _ ) ) }.head )
        ( r2, s2 )
      case Link( mains, name ) =>
        val hypsSeq = Sequent( for ( m <- mains ) yield m -> m.polarity )
        ( ProofLink( name, hypsSeq.map( lctx( _ ) ) ), hypsSeq )
    } )

  def apply( p: LKt, lctx: LocalCtx ): LKProof = withMap( p, lctx )._1
}

